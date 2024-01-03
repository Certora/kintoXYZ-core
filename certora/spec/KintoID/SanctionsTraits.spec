import "setup.spec";

use invariant AdminRoleIsDefaultRole filtered{f -> !upgradeMethods(f)}
use invariant lastMonitoredAtInThePast filtered{f -> !upgradeMethods(f)}

methods {
    function isSanctioned(address, uint16) external returns (bool);
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Ghost & hooks: sanctions meta data                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
ghost mapping(address => uint8) _sanctionsCount;

hook Sload uint8 count _kycmetas[KEY address account].sanctionsCount STORAGE {
    require _sanctionsCount[account] == count;
}

hook Sstore _kycmetas[KEY address account].sanctionsCount uint8 count (uint8 count_old) STORAGE {
    require _sanctionsCount[account] == count_old;
    _sanctionsCount[account] = count;
}

function getSanctionsCount(address account) returns uint8 {
    return _sanctionsCount[account];
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: sanctions                                                                              │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

invariant hasSanctionCountIsNonZero(env e1, address account, uint16 CID)
    isSanctioned(e1, account, CID) => getSanctionsCount(account) > 0
    filtered{f -> !upgradeMethods(f)}
    {
        preserved with (env e2) {require e2.block.timestamp == e1.block.timestamp;}
    }
    

rule onlySanctionMethodCanSanction(method f) filtered{f -> !viewOrUpgrade(f)} {
    address account; uint16 CID;
    env e;

    bool sanctioned_before = isSanctioned(e, account, CID);
        calldataarg args;
        f(e, args);
    bool sanctioned_after = isSanctioned(e, account, CID);

    assert !sanctioned_before && sanctioned_after =>
        f.selector == sig:addSanction(address,uint16).selector;
    assert sanctioned_before && !sanctioned_after =>
        f.selector == sig:removeSanction(address,uint16).selector;
}

rule addSanctionIntegrity(address account, uint16 CID) {
    address account_B;
    uint16 CID_B;
    env e1;
    bool sanctioned_before = isSanctioned(e1, account_B, CID_B);
    uint8 count_before = getSanctionsCount(account_B);
        addSanction(e1, account, CID);
    bool sanctioned_after = isSanctioned(e1, account_B, CID_B);
    uint8 count_after = getSanctionsCount(account_B);
    
    assert (account == account_B && CID == CID_B) =>
        sanctioned_after, "adding a sanction must turn on the sanction";
    assert !(account == account_B && CID == CID_B) =>
        (sanctioned_after == sanctioned_before), "addSanction must change the correct account and country";
    assert (sanctioned_before != sanctioned_after) => count_after - count_before == 1,
        "The number of sanctions must increase by 1";
}

rule removeSanctionIntegrity(address account, uint16 CID) {
    address account_B;
    uint16 CID_B;
    env e1;
    bool sanctioned_before = isSanctioned(e1, account_B, CID_B);
    uint8 count_before = getSanctionsCount(account_B);
        removeSanction(e1, account, CID);
    bool sanctioned_after = isSanctioned(e1, account_B, CID_B);
    uint8 count_after = getSanctionsCount(account_B);
    
    assert (account == account_B && CID == CID_B) =>
        !sanctioned_after, "removing a sanction must turn off the sanction";
    assert !(account == account_B && CID == CID_B) =>
        (sanctioned_after == sanctioned_before), "addSanction must change the correct account and country";
    assert (sanctioned_before != sanctioned_after) => count_before - count_after == 1,
        "The number of sanctions must decrease by 1";
}

rule addSanctionIdempotent(address account, uint16 CID) {
    env e1;
    bool sanctioned_before = isSanctioned(e1, account, CID);
    storage stateBefore = lastStorage;
        addSanction(e1, account, CID);
    storage stateAfter = lastStorage;

    assert sanctioned_before => stateBefore[currentContract] == stateAfter[currentContract],
        "Adding a sanction a second time shouldn't change anything";
}

rule removeSanctionIdempotent(address account, uint16 CID) {
    env e1;
    bool sanctioned_before = isSanctioned(e1, account, CID);
    storage stateBefore = lastStorage;
        require e1.block.timestamp == lastMonitoredAt();
        removeSanction(e1, account, CID);
    storage stateAfter = lastStorage;

    assert !sanctioned_before => stateBefore[currentContract] == stateAfter[currentContract],
        "Removing a sanction a second time shouldn't change anything";
}

rule addedSanctionCanBeRemoved(address account, uint16 CID) {
    env e1;
    env e2; require e2.msg.value == 0; 
    requireInvariant hasSanctionCountIsNonZero(e1, account, CID);
    requireInvariant hasSanctionCountIsNonZero(e2, account, CID);

    bool hasRole1 = hasRole(KYC_PROVIDER_ROLE(), e1.msg.sender);
    bool hasRole2 = hasRole(KYC_PROVIDER_ROLE(), e2.msg.sender);
    addSanction(e1, account, CID);
    assert hasRole1;

    removeSanction@withrevert(e2, account, CID);
    assert hasRole2 => !lastReverted;
}

rule removedSanctionCanBeAdded(address account, uint16 CID) {
    env e1;
    env e2; require e2.msg.value == 0;
    requireInvariant hasSanctionCountIsNonZero(e1, account, CID);
    requireInvariant hasSanctionCountIsNonZero(e2, account, CID);

    bool hasRole1 = hasRole(KYC_PROVIDER_ROLE(), e1.msg.sender);
    bool hasRole2 = hasRole(KYC_PROVIDER_ROLE(), e2.msg.sender);
    removeSanction(e1, account, CID);
    assert hasRole1;

    addSanction@withrevert(e2, account, CID);
    assert hasRole2 => !lastReverted;
}

rule addedTraitCanBeRemoved(address account, uint8 TID) {
    env e1;
    env e2; require e2.msg.value == 0;

    bool hasRole1 = hasRole(KYC_PROVIDER_ROLE(), e1.msg.sender);
    bool hasRole2 = hasRole(KYC_PROVIDER_ROLE(), e2.msg.sender);
    addTrait(e1, account, TID);
    assert hasRole1;

    removeTrait@withrevert(e2, account, TID);
    assert hasRole2 => !lastReverted;
}

rule removeTraitCanBeAdded(address account, uint8 TID) {
    env e1;
    env e2; require e2.msg.value == 0;

    bool hasRole1 = hasRole(KYC_PROVIDER_ROLE(), e1.msg.sender);
    bool hasRole2 = hasRole(KYC_PROVIDER_ROLE(), e2.msg.sender);
    removeTrait(e1, account, TID);
    assert hasRole1;

    addTrait@withrevert(e2, account, TID);
    assert hasRole2 => !lastReverted;
}

rule noncesIncreaseCorrectly(method f) filtered{f -> !viewOrUpgrade(f)} {
    address signerA;
    address signerB;

    uint256 nonceA_before = nonces(signerA);
    uint256 nonceB_before = nonces(signerB);
        env e;
        calldataarg args;
        f(e, args);
    uint256 nonceA_after = nonces(signerA);
    uint256 nonceB_after = nonces(signerB);

    assert nonceA_before == nonceA_after || 
        nonceA_after - nonceA_before == 1, "nonces can increase by 1 at most";
    assert (nonceA_before != nonceA_after) && (nonceB_before != nonceB_after) =>
        signerA == signerB, "A nonce could only change for one signer at a time";
}
