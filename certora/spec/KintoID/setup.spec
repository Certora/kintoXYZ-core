using KintoIDHarness as kintoID;
using KYCViewer as viewer;

methods {
    /// IERC1822ProxiableUpgradeable
    function _.proxiableUUID() external => ERC1822ProxiableUUID(calledContract) expect bytes32;

    /// KintoID
    function lastMonitoredAt() external returns(uint256) envfree;

    /// KYCViewer
    function viewer.isKYC(address _address) external returns (bool);
    function viewer.isSanctionsSafe(address _account) external returns (bool);
    function viewer.isSanctionsSafeIn(address _account, uint16 _countryId) external returns (bool);
    function viewer.isCompany(address _account) external returns (bool) envfree;
    function viewer.isIndividual(address _account) external returns (bool) envfree;
}

ghost ERC1822ProxiableUUID(address) returns bytes32;

definition transferMethods(method f) returns bool = 
    f.selector == sig:transferFrom(address,address,uint256).selector ||
    f.selector == sig:safeTransferFrom(address,address,uint256).selector ||
    f.selector == sig:safeTransferFrom(address,address,uint256,bytes).selector;

definition upgradeMethods(method f) returns bool = 
    f.selector == sig:upgradeToAndCall(address,bytes).selector;

definition viewOrUpgrade(method f) returns bool = upgradeMethods(f) || f.isView;

definition senderIsSelf(env e) returns bool = e.msg.sender == currentContract;

invariant lastMonitoredAtInThePast(env e)
    e.block.timestamp >= lastMonitoredAt()
    {
        preserved with (env eP) {
            require e.block.timestamp == eP.block.timestamp;
        }
    }