import "setup.spec";

rule monitorSanctionsCommutative(address account) {
    address[] accounts = [account];
    IKintoID.MonitorUpdateData data1;
    IKintoID.MonitorUpdateData data2;

    IKintoID.MonitorUpdateData[][] traits1 = [[data1,data2]];
    IKintoID.MonitorUpdateData[][] traits2 = [[data2,data1]];

    env e;
    storage initState = lastStorage;
        monitor(e, accounts, traits1) at initState;
    storage state1 = lastStorage;
        monitor(e, accounts, traits1) at initState;
    storage state2 = lastStorage;

    assert state1[currentContract] == state2[currentContract];
}

rule monitorSanctionsAssociative(address account) {
    address[] accounts = [account];
    IKintoID.MonitorUpdateData data1;
    IKintoID.MonitorUpdateData data2;

    IKintoID.MonitorUpdateData[][] traits1 = [[data1]];
    IKintoID.MonitorUpdateData[][] traits2 = [[data2]];
    IKintoID.MonitorUpdateData[][] traits12 = [[data1,data2]];

    env e;
    storage initState = lastStorage;
        monitor(e, accounts, traits1) at initState;
        monitor(e, accounts, traits2);
    storage state1 = lastStorage;
        monitor(e, accounts, traits12) at initState;
    storage state2 = lastStorage;

    assert state1[currentContract] == state2[currentContract];
}

rule monitorAccountsAssociative(address account1, address account2) {
    address[] accounts1 = [account1];
    address[] accounts2 = [account2];
    address[] accounts12 = [account1, account2];
    IKintoID.MonitorUpdateData data1;
    IKintoID.MonitorUpdateData data2;

    IKintoID.MonitorUpdateData[][] traits1 = [[data1]];
    IKintoID.MonitorUpdateData[][] traits2 = [[data2]];
    IKintoID.MonitorUpdateData[][] traits12 = [[data1],[data2]];

    env e;
    storage initState = lastStorage;
        monitor(e, accounts1, traits1) at initState;
        monitor(e, accounts2, traits2);
    storage state1 = lastStorage;
        monitor(e, accounts12, traits12) at initState;
    storage state2 = lastStorage;

    assert state1[currentContract] == state2[currentContract];
}

rule monitorAccountsCommutative(address account1, address account2) {
    address[] accounts1 = [account1, account2];
    address[] accounts2 = [account2, account1];
    IKintoID.MonitorUpdateData data;

    IKintoID.MonitorUpdateData[][] traits = [[data],[data]];

    env e;
    storage initState = lastStorage;
        monitor(e, accounts1, traits) at initState;
    storage state1 = lastStorage;
        monitor(e, accounts2, traits) at initState;
    storage state2 = lastStorage;

    assert state1[currentContract] == state2[currentContract];
}

rule monitorSanctionsCannotFrontRun(address account) {
    address[] accounts = [account];
    
    IKintoID.MonitorUpdateData data1;
    IKintoID.MonitorUpdateData data2;
    IKintoID.MonitorUpdateData[][] traits1 = [[data1]];
    IKintoID.MonitorUpdateData[][] traits2 = [[data2]];

    env e1;
    env e2;
    require e1.block.timestamp >= e2.block.timestamp;

    storage initState = lastStorage;
    monitor(e1, accounts, traits1) at initState;

    monitor(e2, accounts, traits2) at initState;
    monitor@withrevert(e1, accounts, traits1);

    assert !lastReverted;
}

rule monitorAccountsCannotFrontRun(address account1, address account2) {
    address[] accounts1 = [account1];
    address[] accounts2 = [account2];
    
    IKintoID.MonitorUpdateData data1;
    IKintoID.MonitorUpdateData data2;
    IKintoID.MonitorUpdateData[][] traits1 = [[data1]];
    IKintoID.MonitorUpdateData[][] traits2 = [[data2]];

    env e1;
    env e2;
    require e1.block.timestamp >= e2.block.timestamp;
    require account1 != account2;

    storage initState = lastStorage;
    monitor(e1, accounts1, traits1) at initState;

    monitor(e2, accounts2, traits2) at initState;
    monitor@withrevert(e1, accounts1, traits1);

    assert !lastReverted;
}

