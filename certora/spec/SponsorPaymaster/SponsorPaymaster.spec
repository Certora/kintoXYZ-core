import "setup.spec";
import "../Initializable.spec";

use rule cannotInitializeIfDisabled;
use invariant initializingIsDisabled filtered{f -> !upgradeMethods(f)}

invariant PaymasterEthSolvency()
    to_mathint(getDeposit()) >= sumOfUserBalances
    filtered{f -> !upgradeMethods(f)}
    {
        preserved with (env e) {
            require !senderIsSelf(e);
            //require owner() != currentContract;
        }
    }

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

rule contractSpendsMustDecreaseBalance(method f, address app) filtered{f -> !viewOrUpgrade(f)} {
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
    {
        assert rate_lastOperationTime_before == rate_lastOperationTime_after;
        assert rate_operationCount_before == rate_operationCount_after;
        assert rate_ethCostCount_before == rate_ethCostCount_after;
        assert cost_lastOperationTime_before == cost_lastOperationTime_after;
        assert cost_operationCount_before == cost_operationCount_after;
        assert cost_ethCostCount_before == cost_ethCostCount_after;
        assert total_lastOperationTime_before == total_lastOperationTime_after;
        assert total_operationCount_before == total_operationCount_after;
        assert total_ethCostCount_before == total_ethCostCount_after;
    }
    assert amount_before <= amount_after, "No one can reduce the deposit amount of another";
    if(f.selector == sig:initialize(address).selector) {
        assert unlockBlock_before != unlockBlock_after => account == owner();
    }
    else {
        assert unlockBlock_before == unlockBlock_after;
    }
}
