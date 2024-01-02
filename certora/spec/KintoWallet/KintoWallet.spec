import "setup.spec";

invariant AllowedSignerPolicy()
    signerPolicy() == SINGLE_SIGNER() ||
    signerPolicy() == MINUS_ONE_SIGNER() ||
    signerPolicy() == ALL_SIGNERS();

invariant NumberOfOwnersIntegrity()
    require_uint256(MAX_SIGNERS()) >= getOwnersCount() && getOwnersCount() > 0;

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