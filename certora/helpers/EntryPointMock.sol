// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.12;

import { StakeManager } from "lib/account-abstraction/contracts/core/StakeManager.sol";

interface IEntryPoint {
    function walletFactory() external view returns (address);
    function setWalletFactory(address _walletFactory) external;
}

contract EntryPointMock is StakeManager, IEntryPoint {
    address public walletFactory;

    function setWalletFactory(address _walletFactory) external {
        require(walletFactory == address(0), "AA36 wallet factory already set");
        walletFactory = _walletFactory;
    }

    function decodeContext(bytes calldata context) external pure returns (address,address,uint256) {
        (address account, address userAccount, uint256 gasPricePostOp) =
            abi.decode(context, (address, address, uint256));
        return (account, userAccount, gasPricePostOp);
    }
}