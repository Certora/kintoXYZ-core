methods {
    /// KintoWallet
    function entryPoint() external returns (address) envfree;
    function getNonce() external returns (uint) envfree;
    function getOwnersCount() external returns (uint) envfree;
    function isTokenApproved(address,address) external returns (uint256) envfree;
    //function owners() external returns (address[] memory) envfree;
    function recoverer() external returns (address) envfree;
    function funderWhitelist(address) external returns (bool) envfree;
    function appSigner(address) external returns (address) envfree;
    function appWhitelist(address) external returns (bool) envfree;
    function getOwnersCount() external returns (uint) envfree;
    function signerPolicy() external returns (uint8) envfree;
    function SINGLE_SIGNER() external returns (uint8) envfree;
    function MINUS_ONE_SIGNER() external returns (uint8) envfree;
    function ALL_SIGNERS() external returns (uint8) envfree;
    function MAX_SIGNERS() external returns (uint8) envfree;

    //function KintoWallet._getAppContract(bytes calldata) internal returns (address) => NONDET;

    /// IKintoID
    function _.isKYC(address account) external with (env e) => isKYC_CVL(e.block.timestamp, account) expect bool;

    /// IERC20
    function _.approve(address,uint256) external => NONDET;
}

definition senderIsSelf(env e) returns bool = e.msg.sender == currentContract;

definition entryPointPriviliged(method f) returns bool = 
    f.selector == sig:execute(address,uint256,bytes).selector ||
    f.selector == sig:executeBatch(address[],uint256[],bytes[]).selector ||
    f.selector == sig:validateUserOp(KintoWallet.UserOperation,bytes32,uint256).selector;

/// Mock for the KintoID.isKYC(uint256 timestamp, address account) function.
function isKYC_CVL(uint256 time, address account) returns bool {
    return _isKYC[time][account];
}

persistent ghost mapping(uint256 => mapping(address => bool)) _isKYC;