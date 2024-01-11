import "setup.spec";

invariant AllowedSignerPolicy()
    signerPolicy() == SINGLE_SIGNER() ||
    signerPolicy() == MINUS_ONE_SIGNER() ||
    signerPolicy() == ALL_SIGNERS();

invariant ZeroAddressApp()
    appSigner(0) == 0;

invariant NumberOfOwnersIntegrity()
    require_uint256(MAX_SIGNERS()) >= getOwnersCount()
    {
        preserved initialize(address anOwner, address recover) with (env e) {
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

invariant OwnerListIntegrity()
    ( getOwnersCount() == 2 => (owners(0) != owners(1) && owners(1) !=0) ) &&
    ( getOwnersCount() == 3 => (owners(0) != owners(1) && owners(0) != owners(2) && owners(1) != owners(2)) )
    {
        preserved {
            requireInvariant NumberOfOwnersIntegrity();
        }
    }

invariant SignerPolicyCannotExceedOwnerCount()
    signerPolicy() == MINUS_ONE_SIGNER() => getOwnersCount() > 1
    {
        preserved {
            requireInvariant AllowedSignerPolicy();
            requireInvariant NumberOfOwnersIntegrity();
        }
    }

invariant FirstOwnerIsKYC(env e)
    (e.block.timestamp > 0 && getOwnersCount() > 0) => (
        (inRecovery() == 0 => isKYC_CVL(e.block.timestamp, owners(0)))
    )
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

/// In-progress:
rule cannotValidateTheSameOpTwice(KintoWallet.UserOperation userOp) {
    env e1;
    env e2;
    require e1.msg.sender == e2.msg.sender;
    require e1.msg.value == e2.msg.value;
    require isKYC_CVL(e1.block.timestamp, owners(0)) == isKYC_CVL(e2.block.timestamp, owners(0));
    
    bytes32 userOpHash1; uint256 missingAccountFunds1;
    bytes32 userOpHash2; uint256 missingAccountFunds2;
    
    uint256 data1 = validateUserOp(e1, userOp, userOpHash1, missingAccountFunds1);
    uint256 data2 = validateUserOp@withrevert(e2, userOp, userOpHash2, missingAccountFunds2);

    if(userOpHash1 == userOpHash2 && missingAccountFunds1 == missingAccountFunds2) {
        assert !lastReverted;
        assert data1 == data2;
    }
    assert true;
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