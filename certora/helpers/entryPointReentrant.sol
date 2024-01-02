// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.12;

import {IEntryPoint} from "@aa/interfaces/IEntryPoint.sol";

contract entryPointReentrant {
    /// fucntion selector for entry
    enum entrySelector {
        Null, 
        AddStake, 
        Unlock, 
        WithdrawStake, 
        WithdrawTo,
        Fallback
    } 
    IEntryPoint public immutable entryPoint;
    entrySelector private _selector;
    bytes private _reentrancyData;

    constructor(IEntryPoint _entryPoint) {
        entryPoint = _entryPoint;
    }

    function setEntrySelector(entrySelector newSelector) external {
        _selector = newSelector;
    }

    receive() payable external {
        bytes memory data;
        uint256 value;
        if(_selector == entrySelector.AddStake) {
            value = msg.value;
            uint32 unstakeDelaySec = abi.decode(_reentrancyData, (uint32));
            data =  abi.encodeWithSelector(entryPoint.addStake.selector, unstakeDelaySec);
        }
        else if(_selector == entrySelector.Unlock) {
           data = abi.encodeWithSelector(entryPoint.unlockStake.selector);
        }
        else if(_selector == entrySelector.WithdrawStake) {
            address payable withdrawAddress = abi.decode(_reentrancyData, (address));
            data = abi.encodeWithSelector(entryPoint.withdrawStake.selector, withdrawAddress);
        }
        else if(_selector == entrySelector.WithdrawTo) {
            (address payable withdrawAddress, uint256 withdrawAmount) = 
                abi.decode(_reentrancyData, (address,uint256));
             data = abi.encodeWithSelector(entryPoint.withdrawTo.selector, withdrawAddress, withdrawAmount);
        }
        else if(_selector == entrySelector.Fallback) {
            data = "";
        }
        else {
            /// Do nothing. Accept transfer.
            return;
        }
        address(entryPoint).call{value : value}(data);
    }
}
