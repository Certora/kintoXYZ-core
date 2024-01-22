import "setup.spec";
import "../Initializable.spec";

use rule cannotInitializeIfDisabled;
use invariant initializingIsDisabled filtered{f -> !upgradeMethods(f)}

/// @title The sum of user balances is covered by the EntryPoint deposit of the Paymaster.
invariant PaymasterEthSolvency()
    to_mathint(getDeposit()) >= sumOfUserBalances
    filtered{f -> !upgradeMethods(f)}
    {
        preserved with (env e) {
            require !senderIsSelf(e);
        }
    }

/// @title The gas cost post-op cannot depend on the user address.
/// The contract spent can only change for the post-op context account.
rule postOpGasCostIsUserFree() {
    env e;
    IPaymaster.PostOpMode modeA;
    IPaymaster.PostOpMode modeB;
    bytes contextA; uint256 priceA; address accountA; 
        accountA, _, priceA = contextDecode(contextA);
    bytes contextB;  uint256 priceB; address accountB;
        accountB, _, priceB = contextDecode(contextB);
    uint256 actualGasCost;
    storage initState = lastStorage;

    uint256 spentA_0 = contractSpent(accountA);
    uint256 spentB_0 = contractSpent(accountB);

    postOp(e, modeA, contextA, actualGasCost) at initState;
    uint256 spentA_1 = contractSpent(accountA);
    uint256 spentB_1 = contractSpent(accountB);
    
    postOp(e, modeB, contextB, actualGasCost) at initState;
    uint256 spentA_2 = contractSpent(accountA);
    uint256 spentB_2 = contractSpent(accountB);

    assert accountA != accountB => spentB_0 == spentB_1, "The contract spent gas could only change for the account";
    assert accountA != accountB => spentA_0 == spentA_2, "The contract spent gas could only change for the account";
    assert priceB == priceA => spentA_1 - spentA_0 == spentB_2 - spentB_0, 
        "If the gas price doesn't change between calls, then the spent amount shouldn't changed";
}

/// @title The balance of any account can only increase by addDepositFor().
rule balanceOnlyIncreasesByDeposit(address account, method f) filtered{f -> !viewOrUpgrade(f)} {
    uint256 balanceBefore = balances(account);
        env e;
        calldataarg args;
        f(e,args);
    uint256 balanceAfter = balances(account);

    assert balanceAfter > balanceBefore => f.selector == sig:addDepositFor(address).selector;
}

/*rule canStakeAndWithdrawIfTimeElapses() {
    env e1;
    env e2;
    env e3;
    require e1.msg.sender == e2.msg.sender;
    require e3.msg.sender == e2.msg.sender;
    require e2.block.number >= e1.block.number;
    require e3.block.number >= e2.block.number;
    require e2.block.number == e2.block.number;
    require e1.block.number !=0;

    initializeSumOfBalances();
    requireInvariant PaymasterEthSolvency();
    require getDeposit() + nativeBalances[e2.msg.sender] <= max_uint;
    storage initState = lastStorage;
    
    address account = e2.msg.sender;
    uint256 amount = e1.msg.value;
    address target;
    withdrawTokensTo(e3, target, 0) at initState;

    addDepositFor(e1, account) at initState;
    unlockTokenDeposit(e2);
    withdrawTokensTo@withrevert(e3, target, amount);

    assert lastReverted <=> e1.block.number == e3.block.number;
} */

/// @title The balance of any account can decrease at most by the MAX_COST_OF_USEROP().
rule balanceDecreaseIsAtMostMaxOpCost(address account, method f) 
filtered{f -> !viewOrUpgrade(f) &&
    f.selector != sig:withdrawTokensTo(address,uint256).selector &&
    f.selector != sig:withdrawTo(address,uint256).selector} 
{    
    uint256 balanceBefore = balances(account);
        env e;
        calldataarg args;
        f(e,args);
    uint256 balanceAfter = balances(account);

    assert balanceAfter < balanceBefore => balanceBefore - balanceAfter <= to_mathint(MAX_COST_OF_USEROP());
}

/// @title No operation can front-run validatePaymasterUserOp() and make it revert.
rule noOperationFrontRunsValidate(method f) 
filtered{f -> !f.isView && !(f.selector == 
    sig:validatePaymasterUserOp(SponsorPaymaster.UserOperation,bytes32,uint256).selector)} {
    
    env e1; calldataarg args1;
    env e2; calldataarg args2;
    //require e1.msg.sender != e2.msg.sender;
    storage initState = lastStorage;

    validatePaymasterUserOp(e1, args1) at initState;

    f(e2, args2) at initState;
    validatePaymasterUserOp@withrevert(e1, args1);

    assert !lastReverted;
}

/// @title No operation can change the context output of validatePaymasterUserOp(). 
rule validationContextIsConsistent(method f) 
filtered{f -> !f.isView && f.selector != 
    sig:validatePaymasterUserOp(SponsorPaymaster.UserOperation,bytes32,uint256).selector} {
    env e1; calldataarg args1;
    env e2; calldataarg args2;
    //require e1.msg.sender != e2.msg.sender;
    storage initState = lastStorage;
    bytes context1; uint256 data1;
    bytes context2; uint256 data2;

    context1, data1 = validatePaymasterUserOp(e1, args1) at initState;
    address account1; address userAccount1; uint256 gasPricePostOp1;
    account1, userAccount1, gasPricePostOp1 = contextDecode(context1);

    f(e2, args2) at initState;
    context2, data2 = validatePaymasterUserOp(e1, args1);
    address account2; address userAccount2; uint256 gasPricePostOp2;
    account2, userAccount2, gasPricePostOp2 = contextDecode(context2);

    assert data1 == data2, "No operation should alter the validation data";
    assert account1 == account2 && 
        userAccount1 == userAccount2 && 
        gasPricePostOp1 == gasPricePostOp2, "No operation should alter the validation context";
}

/// @title A call validatePaymasterUserOp() can never front-run another call to the same function and make it revert.
rule validatePayMasterCannotFrontRunEachOther() {
    env e1;
    env e2;
    SponsorPaymaster.UserOperation userOp1;
    SponsorPaymaster.UserOperation userOp2;
    bytes32 userOpHash1;
    bytes32 userOpHash2;
    uint256 maxCost1;
    uint256 maxCost2;

    storage initState = lastStorage;

    validatePaymasterUserOp(e1, userOp1, userOpHash1, maxCost1) at initState;

    validatePaymasterUserOp(e2, userOp2, userOpHash2, maxCost2) at initState;
    validatePaymasterUserOp@withrevert(e1, userOp1, userOpHash1, maxCost1);

    assert !lastReverted;
}

/// @title The rate, cost and total rate limits last operation time is never in the future.
rule lastOperationTimeIsInThePast(address account, address app, method f) 
filtered{f -> !viewOrUpgrade(f)} {
    uint256 rate_lastOp_before; rate_lastOp_before, _ , _ = rateLimit(account, app);
    uint256 cost_lastOp_before; cost_lastOp_before, _ , _ = costLimit(account, app);
    uint256 total_lastOp_before; total_lastOp_before, _ , _ = totalRateLimit(account);
        env e;
        calldataarg args;
        f(e, args);
        uint256 time = e.block.timestamp;
    uint256 rate_lastOp_after; rate_lastOp_after, _ , _ = rateLimit(account, app);
    uint256 cost_lastOp_after; cost_lastOp_after, _ , _ = costLimit(account, app);
    uint256 total_lastOp_after; total_lastOp_after, _ , _ = totalRateLimit(account);

    assert rate_lastOp_before <= time => rate_lastOp_after <= time;
    assert cost_lastOp_before <= time => cost_lastOp_after <= time;
    assert total_lastOp_before <= time => total_lastOp_after <= time;
}

/// @title The postOp() changes the user limits of the op input context (account and sender) only.
rule postOpUpdatesLimits() {
    env e;
    address sender; address account;
    uint256 count1; uint256 lastOpTime_rate1; uint256 ethCount1; uint256 lastOpTime_cost1;
    uint256 count2; uint256 lastOpTime_rate2; uint256 ethCount2; uint256 lastOpTime_cost2;
    
    count1, lastOpTime_rate1, ethCount1, lastOpTime_cost1 = appUserLimit(sender, account);

    IPaymaster.PostOpMode mode;
    bytes context;
    uint256 gasCost;
    address _account; address _sender;
    _account, _sender, _ = contextDecode(context);
    postOp(e, mode, context, gasCost);
    
    count2, lastOpTime_rate2, ethCount2, lastOpTime_cost2 = appUserLimit(sender, account);

    assert lastOpTime_rate1 != lastOpTime_rate2 => (sender == _sender && account == _account);
}

/// @title Any operation may change the contract spent amount and balance for one app at a time.
rule onlyOneAppBalanceChangeAtATime(method f) filtered{f -> !viewOrUpgrade(f)} {
    env e;
    calldataarg args;
    address app1; address app2;

    uint256 spent1_before = contractSpent(app1);
    uint256 balance1_before = balances(app1);
    uint256 spent2_before = contractSpent(app2);
    uint256 balance2_before = balances(app2);
        f(e, args);
    uint256 spent1_after = contractSpent(app1);
    uint256 balance1_after = balances(app1);
    uint256 spent2_after = contractSpent(app2);
    uint256 balance2_after = balances(app2);

    assert (spent1_before != spent1_after && app1 != app2) => spent2_before == spent2_after;
    assert (balance1_before != balance1_after && app1 != app2) => balance2_before == balance2_after;
}

/// @title The contract spent amount cannot decrease, and must increase by the same amount the balance of that contract decreases.
rule contractSpentMustDecreaseBalance(method f, address app) 
filtered{f -> !viewOrUpgrade(f)} {
    env e;
    calldataarg args;
    uint256 spentBefore = contractSpent(app);
    uint256 balanceBefore = balances(app);
        f(e, args);
    uint256 spentAfter = contractSpent(app);
    uint256 balanceAfter = balances(app);
    mathint totalSpent = spentAfter - spentBefore;

    assert totalSpent >=0, "Spent amount cannot decrease";
    assert totalSpent !=0 => balanceBefore - balanceAfter == totalSpent, 
        "The spent amount must be reducted from the app balance";
}

/// @title No operation can front-run and make a call to withdrawTokensTo() revert.
rule cannotDos_withdrawTokensTo(method f) 
filtered{f -> !viewOrUpgrade(f)} {
    env e1;
    require e1.block.number > 0;
    address target; uint256 amount;

    initializeSumOfBalances();
    requireInvariant PaymasterEthSolvency();

    env e2;
    require e2.block.number > 0;
    require e2.msg.sender != e1.msg.sender;
    calldataarg args;

    storage initState = lastStorage;
    withdrawTokensTo(e1, target, amount) at initState;

    f(e2, args) at initState;
    withdrawTokensTo@withrevert(e1, target, amount);

    assert !lastReverted;
}

/// @title Only the user (or the EntryPoint) can change his own limits.
rule onlyUserCanChangeHisParameters(address account, method f) 
filtered{f -> !viewOrUpgrade(f)} {
    address app;

    uint256 rate_lastOperationTime_before;
    uint256 rate_operationCount_before;
    uint256 rate_ethCostCount_before;
    uint256 cost_lastOperationTime_before;
    uint256 cost_operationCount_before;
    uint256 cost_ethCostCount_before;
    uint256 total_lastOperationTime_before;
    uint256 total_operationCount_before;
    uint256 total_ethCostCount_before;
    uint256 amount_before; uint256 unlockBlock_before;

    rate_lastOperationTime_before,
    rate_operationCount_before,
    rate_ethCostCount_before = 
        rateLimit(account,app);
    cost_lastOperationTime_before,
    cost_operationCount_before,
    cost_ethCostCount_before = 
        costLimit(account,app);
    total_lastOperationTime_before,
    total_operationCount_before,
    total_ethCostCount_before = 
        totalRateLimit(account);
    amount_before, unlockBlock_before = depositInfo(account);

    env e; require e.msg.sender != account;
    require e.block.number > 0;
    calldataarg args;
    f(e, args);

    uint256 rate_lastOperationTime_after;
    uint256 rate_operationCount_after;
    uint256 rate_ethCostCount_after;
    uint256 cost_lastOperationTime_after;
    uint256 cost_operationCount_after;
    uint256 cost_ethCostCount_after;
    uint256 total_lastOperationTime_after;
    uint256 total_operationCount_after;
    uint256 total_ethCostCount_after;
    uint256 amount_after; uint256 unlockBlock_after;

    rate_lastOperationTime_after,
    rate_operationCount_after,
    rate_ethCostCount_after = 
        rateLimit(account,app);
    cost_lastOperationTime_after,
    cost_operationCount_after,
    cost_ethCostCount_after = 
        costLimit(account,app);
    total_lastOperationTime_after,
    total_operationCount_after,
    total_ethCostCount_after = 
        totalRateLimit(account);
    amount_after, unlockBlock_after = depositInfo(account);
    
    if(e.msg.sender != entryPoint()) {
        assert rate_lastOperationTime_before == rate_lastOperationTime_after;
        assert rate_operationCount_before == rate_operationCount_after;
        assert rate_ethCostCount_before == rate_ethCostCount_after;
        assert cost_lastOperationTime_before == cost_lastOperationTime_after;
        assert cost_operationCount_before == cost_operationCount_after;
        assert cost_ethCostCount_before == cost_ethCostCount_after;
        assert total_lastOperationTime_before == total_lastOperationTime_after;
        assert total_operationCount_before == total_operationCount_after;
        assert total_ethCostCount_before == total_ethCostCount_after;
        assert amount_before <= amount_after, "No one can reduce the deposit amount of another";
    }
    
    if(f.selector == sig:initialize(address).selector) {
        assert unlockBlock_before != unlockBlock_after => account == owner();
    }
    else {
        assert unlockBlock_before == unlockBlock_after;
    }
}