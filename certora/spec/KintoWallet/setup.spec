using MockECDSA as MockECDSA;

methods {
    /// KintoWallet
    function entryPoint() external returns (address) envfree;
    function getNonce() external returns (uint) envfree;
    function getOwnersCount() external returns (uint) envfree;
    function isTokenApproved(address,address) external returns (uint256) envfree;
    function owners(uint256) external returns (address) envfree;
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
    function MockECDSA.recoverMock(bytes32, bytes) external returns (address) envfree;

    function ECDSA.recover(bytes32 hash, bytes memory signature) internal returns (address) => recoverCVL(hash, signature);

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
/// Transaction hash => signature hash => signer.
persistent ghost mapping(bytes32 => mapping(bytes32 => address)) _recoverMap;

function recoverCVL(bytes32 hash, bytes signature) returns address {
    /// First option: CVL mapping
    //return _recoverMap[hash][keccak256(signature)];
    /// Second option: use Solidity implemenation
    return MockECDSA.recoverMock(hash, signature);
}

function isOwner(address account) returns bool {
    uint256 count = getOwnersCount();
    if(count == 1) {return account == owners(0);}
    else if(count == 2) {return account == owners(0) || account == owners(1);}
    else if(count == 3) {return account == owners(0) || account == owners(1) || account == owners(2);}
    return false;
}

persistent ghost mapping(uint256 => mapping(address => bool)) _isKYC;