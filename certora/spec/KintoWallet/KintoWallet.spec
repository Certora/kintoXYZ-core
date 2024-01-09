import "setup.spec";

invariant AllowedSignerPolicy()
    signerPolicy() == SINGLE_SIGNER() ||
    signerPolicy() == MINUS_ONE_SIGNER() ||
    signerPolicy() == ALL_SIGNERS();

invariant ZeroAddressApp()
    appSigner(0) == 0;

invariant NumberOfOwnersIntegrity()
    require_uint256(MAX_SIGNERS()) >= getOwnersCount() && getOwnersCount() > 0;

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