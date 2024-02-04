using KintoIDHarness as kintoID;
using KYCViewer as viewer;

methods {
    /// IERC1822ProxiableUpgradeable
    function _.proxiableUUID() external => ERC1822ProxiableUUID(calledContract) expect bytes32;

    /// KintoID
    function lastMonitoredAt() external returns (uint256) envfree;
    function isSanctionsSafeIn(address,uint16) external returns (bool);
    function nonces(address) external returns (uint256) envfree;
    function KYC_PROVIDER_ROLE() external returns (bytes32) envfree;
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;
    function getRoleAdmin(bytes32) external returns (bytes32) envfree;
    function nextTokenId() external returns (uint256) envfree;

    /// KYCViewer
    function viewer.isKYC(address _address) external returns (bool);
    function viewer.isSanctionsSafe(address _account) external returns (bool);
    function viewer.isSanctionsSafeIn(address _account, uint16 _countryId) external returns (bool);
    function viewer.isCompany(address _account) external returns (bool) envfree;
    function viewer.isIndividual(address _account) external returns (bool) envfree;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Ghost & hooks: sanctions meta data                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
/// Maximum number of sanctions (assumed).
definition MAX_SANCTIONS() returns uint8 = 200;

ghost mapping(address => uint8) _sanctionsCount {
    axiom forall address account. _sanctionsCount[account] <= MAX_SANCTIONS();
}

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

ghost ERC1822ProxiableUUID(address) returns bytes32;

definition transferMethods(method f) returns bool = 
    f.selector == sig:transferFrom(address,address,uint256).selector ||
    f.selector == sig:safeTransferFrom(address,address,uint256).selector ||
    f.selector == sig:safeTransferFrom(address,address,uint256,bytes).selector;

definition upgradeMethods(method f) returns bool = 
    f.selector == sig:upgradeToAndCall(address,bytes).selector;

definition monitorMethods(method f) returns bool = 
    f.selector == sig:monitor(address[],IKintoID.MonitorUpdateData[][]).selector;

definition viewOrUpgrade(method f) returns bool = upgradeMethods(f) || f.isView;

definition senderIsSelf(env e) returns bool = e.msg.sender == currentContract;

/// @title lastMonitoredAt() is never in the future.
invariant lastMonitoredAtInThePast(env e)
    e.block.timestamp >= lastMonitoredAt()
    {
        preserved with (env eP) {
            require e.block.timestamp == eP.block.timestamp;
        }
    }

/// @title The role admin of any role is the DEFAULT_ADMIN_ROLE()
invariant AdminRoleIsDefaultRole(bytes32 role)
    getRoleAdmin(role) == DEFAULT_ADMIN_ROLE()
    {
        preserved with (env e) {require e.msg.sender != 0;}
    }

/// @title Only the DEFAULT_ADMIN_ROLE() can revoke/grant a role from/to an account.
rule onlyRoleAdminRevokesRole(method f, bytes32 role, address account) {
    requireInvariant AdminRoleIsDefaultRole(role);

    bool hasRole_before = hasRole(role, account);
        env e;
        calldataarg args;
        f(e,args);
    bool hasRole_after = hasRole(role, account);

    assert (hasRole_before != hasRole_after && account != e.msg.sender) =>
        hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
}