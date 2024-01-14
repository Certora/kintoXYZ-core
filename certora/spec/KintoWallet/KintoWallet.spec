import "setup.spec";
import "../Initializable.spec";

invariant AllowedSignerPolicy()
    signerPolicy() == SINGLE_SIGNER() ||
    signerPolicy() == MINUS_ONE_SIGNER() ||
    signerPolicy() == ALL_SIGNERS();

invariant ZeroAddressApp()
    appSigner(0) == 0;

invariant NumberOfOwnersIntegrity()
    assert_uint256(MAX_SIGNERS()) >= getOwnersCount()
    {
        preserved initialize(address owner, address recoverer) with (env e) {
            /// Factory initializes right after deployment.
            require getOwnersCount() == 0;
        }
    }

invariant OwnerisNonZero()
    getOwnersCount() > 0 => !isOwner(0)
    {
        preserved initialize(address owner, address recoverer) with (env eP) {
            /// Guaranteed in KintoWalletFactory.createAccount():
            /// require(kintoID.isKYC(owner), 'KYC required');
            /// and on the invariant in KintoID: ZeroAddressNotKYC()
            require owner !=0;
        }
    }

invariant OwnerListNoDuplicates()
    ( getOwnersCount() == 2 => (owners(0) != owners(1) && owners(1) !=0) ) &&
    ( getOwnersCount() == 3 => (owners(0) != owners(1) && owners(0) != owners(2) && owners(1) != owners(2)) )
    {
        preserved {
            requireInvariant NumberOfOwnersIntegrity();
        }
    }

invariant SignerPolicyCannotExceedOwnerCount()
    (initialized != MAX_VERSION()) => (
    (signerPolicy() == SINGLE_SIGNER() => getOwnersCount() >= 1) &&
    (signerPolicy() == MINUS_ONE_SIGNER() => getOwnersCount() > 1) &&
    (signerPolicy() == ALL_SIGNERS() => getOwnersCount() == assert_uint256(MAX_SIGNERS())))
    {
        preserved {
            requireInvariant AllowedSignerPolicy();
            requireInvariant NumberOfOwnersIntegrity();
        }
        preserved execute(address A, uint256 B, bytes C) with (env e) {
            require initialized != MAX_VERSION();
        }
        preserved executeBatch(address[] A, uint256[] B, bytes[] C) with (env e) {
            require initialized != MAX_VERSION();
        }
    }

invariant FirstOwnerIsKYC(env e)
    (e.block.timestamp > 0 && getOwnersCount() > 0) => isKYC_CVL(e.block.timestamp, owners(0))
    /// We assume that when finishing recovery the new owner has already been minted KYC by the providers.
    /// Also, see rule 'firstOwnerIsChangedOnlyByRecovery'.
    filtered{f -> f.selector != sig:finishRecovery(address[]).selector}
    {
        preserved with (env eP) {
            require eP.block.timestamp == e.block.timestamp;
        }
        preserved initialize(address owner, address recoverer) with (env eP) {
            require eP.block.timestamp == e.block.timestamp;
            /// Guaranteed in KintoWalletFactory.createAccount():
            /// require(kintoID.isKYC(owner), 'KYC required');
            require(isKYC_CVL(eP.block.timestamp, owner));
        }
    } 

rule whichFunctionRemovesOwner(address account, method f) filtered{f -> !f.isView} {
    bool ownerBefore = isOwner(account);
        env e;
        calldataarg args;
        f(e, args);
    bool ownerAfter = isOwner(account);

    assert ownerBefore != ownerAfter => isResetSigners(f);
}

rule firstOwnerIsChangedOnlyByRecovery(method f) filtered{f -> !f.isView} {
    address firstOwner_before = owners(0);
        env e;
        calldataarg args;
        f(e, args);
    address firstOwner_after = owners(0);  

    assert firstOwner_after != firstOwner_before => f.selector == sig:finishRecovery(address[]).selector;
}

rule finishRecoveryIntegrity() {
    env e;
    address[] signers;
    finishRecovery(e, signers);
    assert owners(0) == signers[0];
    assert owners(1) == signers[1];
    assert owners(2) == signers[2];
}

/// If the validation succeeds, the signer's identity must correct (owner or app signer).
rule validationSignerIntegrity() {
    env e;
    requireInvariant NumberOfOwnersIntegrity();
    requireInvariant OwnerisNonZero();
    requireInvariant SignerPolicyCannotExceedOwnerCount();
    require initialized != MAX_VERSION();

    KintoWallet.UserOperation userOp;
    bytes32 userOpHash;
    uint256 missingAccountFunds;
    uint256 validationData = validateUserOp(e, userOp, userOpHash, missingAccountFunds);
    /// Assuming the validation succeeded:
    require validationData == 0;
    /// App from userOp:
    address app = ghostAppContract;
    /// userOp hash + Eth signature hash:
    bytes32 hash = signedMessageHash(userOpHash);
    /// Hash message signer:
    address signer = recoverCVL(hash, userOp.signature);
    
    bool appHasSigner = (app !=0 && appSigner(app) !=0);

    assert !appHasSigner => isOwner(signer), "Owner must be signer of wallet transaction";
    assert appHasSigner => appSigner(app) == signer, "App signer must sign for app transaction";
}


rule entryPointPriviligedFunctions(method f) 
filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    f(e, args);
    assert entryPointPriviliged(f) => e.msg.sender == entryPoint();
}

rule whichFunctionsChangeWhiteList(address app, method f) filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    bool isWhiteList_before = appWhitelist(app);
        f(e, args);
    bool isWhiteList_after = appWhitelist(app);
    
    assert isWhiteList_after != isWhiteList_before =>
        f.selector == sig:setAppWhitelist(address[],bool[]).selector && senderIsSelf(e);
}

rule whichFunctionsChangeFunderWhiteList(address app, method f) filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    bool isWhiteList_before = funderWhitelist(app);
        f(e, args);
    bool isWhiteList_after = funderWhitelist(app);

    assert isWhiteList_after != isWhiteList_before => 
        f.selector == sig:setFunderWhitelist(address[],bool[]).selector && senderIsSelf(e);
}

rule whichFunctionsChangeAppSigner(address app, method f) filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    address signer_before = appSigner(app);
        f(e, args);
    address signer_after = appSigner(app);
    
    assert signer_before != signer_after => 
        f.selector == sig:setAppKey(address,address).selector && senderIsSelf(e);
}