pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract Reward {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner;

    // data structure for investors
    struct Investor {
        uint256 freeBalance;
        uint256 lockedBalance;
    }
    Set.Data private enodes;
    mapping(address => Investor) public investors;
    mapping(uint256 => mapping(address => bool)) returned; // record investors who have claimed interests for each round
    mapping(uint256 => uint256) public investments;
    uint256 public totalFreeBalance;
    uint256 public totalLockedBalance;

    // states controllers
    bool public inRaise = false;
    bool public inLock = false;
    bool public inSettlement = false;


    // modifiers
    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }
    modifier duringRaise() {
        require(inRaise == true);
        _;
    }
    modifier duringLock() {
        require(inLock == true);
        _;
    }
    modifier duringSettlement() {
        require(inSettlement == true);
        _;
    }

    constructor () public {
        owner = msg.sender;
    }


    // configs
    uint256 public bonusPool;
    mapping(uint256 => uint256) public bonus;
    uint256 public raisePeriod = 3 days;
    uint256 public lockPeriod = 84 days;
    uint256 public settlementPeriod = 3 days;
    uint256 public enodeThreshold = 20000 ether;
    uint256 public round = 0;
    uint256 public nextRaiseTime = 0;
    uint256 public nextLockTime = 0;
    uint256 public nextSettlementTime = 0;


    // events
    event FundBonusPool(address who, uint256 amount, uint256 total);
    event SetConfig(string what, uint256 value);
    event SetTime(string what, uint256 when);
    event NewRaise(uint256 when);
    event NewEnode(address who, uint256 investment);
    event EnodeQuit(address who, uint256 balance);
    event AddInvestment(address who, uint256 amount, uint256 total);
    event SubInvestment(address who, uint256 amount, uint256 total);
    event NewLock(uint256 when);
    event NewSettlement(uint256 when);
    event ApplyForSettlement(address who, uint256 income);


    // get enodes
    function getEnodes() public view returns(address[]) {
        return enodes.getAll();
    }

    function freeBalanceOf(address investor) view returns(uint256) {
        return investors[investor].freeBalance;
    }

    function lockedBalanceOf(address investor) view returns(uint256) {
        return investors[investor].lockedBalance;
    }

    function totalBalanceOf(address investor) view returns(uint256) {
        return investors[investor].freeBalance.add(investors[investor].lockedBalance);
    }

    // set configs
    // set raise period
    function setRaisePeriod(uint256 _raisePeriod) public onlyOwner {
        raisePeriod = _raisePeriod;
        emit SetConfig("raise period", raisePeriod);
    }

    // set lock period
    function setLockPeriod(uint256 _lockPeriod) public onlyOwner {
        lockPeriod = _lockPeriod;
        emit SetConfig("lock period", lockPeriod);
    }

    // set settlement period
    function setSettlementPeriod(uint256 _settlementPeriod) public onlyOwner {
        settlementPeriod = _settlementPeriod;
        emit SetConfig("settlement period", settlementPeriod);
    }

    // set threshold to become a enode
    function setEnodeThreshold(uint256 _enodeThreshold) public onlyOwner {
        enodeThreshold = _enodeThreshold;
        emit SetConfig("enode threshold", enodeThreshold);
    }

    // state change
    // start a new raise
    function newRaise() public onlyOwner {
        if(round > 0) {
            require(now >= nextRaiseTime.sub(1 days)); // 1 day as a buffer
        }
        inRaise = true;
        inLock = false;
        inSettlement = false;
        round = round.add(1);
        nextLockTime = now.add(raisePeriod);
        assert(totalFreeBalance.add(bonusPool) == address(this).balance);
        assert(totalLockedBalance == 0);
        emit SetTime("next lock time", nextLockTime);
        emit NewRaise(now);
    }

    // fund bonus pool
    function () public payable duringRaise {
        bonusPool = bonusPool.add(msg.value);
        assert(totalFreeBalance.add(bonusPool) == address(this).balance);
        assert(totalLockedBalance == 0);
        emit FundBonusPool(msg.sender, msg.value, bonusPool);
    }

    // investors can only submit deposit during raise
    function deposit() public payable duringRaise {
        investors[msg.sender].freeBalance = investors[msg.sender].freeBalance.add(msg.value);
        totalFreeBalance = totalFreeBalance.add(msg.value);
        emit AddInvestment(msg.sender, msg.value, totalFreeBalance);
        if(investors[msg.sender].freeBalance >= enodeThreshold) {
            enodes.insert(msg.sender);
            emit NewEnode(msg.sender, investors[msg.sender].freeBalance);
        }
        assert(totalFreeBalance.add(bonusPool) == address(this).balance);
        assert(totalLockedBalance == 0);
    }

    // investors can only withdraw free balance
    function withdraw(uint amount) public {
        require(amount <= investors[msg.sender].freeBalance);
        msg.sender.transfer(amount);
        investors[msg.sender].freeBalance = investors[msg.sender].freeBalance.sub(amount);
        totalFreeBalance = totalFreeBalance.sub(amount);
        emit SubInvestment(msg.sender, amount, totalFreeBalance);
        if(investors[msg.sender].freeBalance < enodeThreshold) {
            enodes.remove(msg.sender);
            emit EnodeQuit(msg.sender, investors[msg.sender].freeBalance);
        }
        assert(totalFreeBalance.add(bonusPool).add(totalLockedBalance) == address(this).balance);
    }

    function lockDeposit(address enode) public onlyOwner duringLock {
        assert(investors[enode].lockedBalance == 0);
        investors[enode].lockedBalance = investors[enode].freeBalance;
        totalLockedBalance = totalLockedBalance.add(investors[enode].lockedBalance);
        investors[enode].freeBalance = 0;
        totalFreeBalance = totalFreeBalance.sub(investors[enode].lockedBalance);
        investments[round] = investments[round].add(investors[enode].lockedBalance);
        assert(totalFreeBalance.add(bonusPool).add(totalLockedBalance) == address(this).balance);
    }

    function lockAllDeposit() public onlyOwner duringLock {
        for(uint i=0; i<enodes.values.length; i++) {
            lockDeposit(enodes.values[i]);
        }
    }

    function onlyNewLock() public onlyOwner {
        require(now >= nextLockTime.sub(1 days));
        inRaise = false;
        inLock = true;
        inSettlement = false;
        nextSettlementTime = now.add(lockPeriod);
        bonus[round] = bonusPool;
        emit SetTime("next settlement time", nextSettlementTime);
        emit NewLock(now);
    }

    // start a new lock period
    function newLock() public onlyOwner {
        onlyNewLock();
        lockAllDeposit();
    }

    // start a new settlement
    function onlyNewSettlement() public onlyOwner {
        require(now >= nextSettlementTime.sub(1 days));
        inRaise = false;
        inLock = false;
        inSettlement = true;
        nextRaiseTime = now.add(settlementPeriod);
        emit SetTime("next raise time", nextRaiseTime);
        emit NewSettlement(now);
    }

    // calculate interest
    function settle(address investor) public onlyOwner duringSettlement {
        require(!returned[round][investor]);
        require(enodes.contains(investor));
        uint256 interest;
        interest = bonus[round].mul(investors[investor].lockedBalance).div(investments[round]);
        investors[investor].freeBalance = investors[investor].freeBalance.add(interest).add(investors[investor].lockedBalance);
        totalLockedBalance = totalLockedBalance.sub(investors[investor].lockedBalance);
        investors[investor].lockedBalance = 0;
        totalFreeBalance = totalFreeBalance.add(investors[investor].freeBalance);
        bonusPool = bonusPool.sub(interest);
        returned[round][investor] = true;
        emit ApplyForSettlement(investor, interest);
    }

    function settleAll() public onlyOwner duringSettlement {
        for(uint j=0; j<enodes.values.length; j++) {
            settle(enodes.values[j]);
        }
    }

    function newSettlement() public onlyOwner {
        onlyNewSettlement();
        settleAll();
    }

    // backup
    // set next raise time.
    function setNextRaiseTime(uint256 _nextRaiseTime) public onlyOwner {
        nextRaiseTime = _nextRaiseTime;
        emit SetTime("next raise time", nextRaiseTime);
    }

    // set next lock time.
    function setNextLockTime(uint256 _nextLockTime) public onlyOwner {
        nextLockTime = _nextLockTime;
        emit SetTime("next lock time", nextLockTime);
    }

    // set next settlement time.
    function setNextSettlementTime(uint256 _nextSettlementTime) public onlyOwner {
        nextSettlementTime = _nextSettlementTime;
        emit SetTime("next settlement time", nextSettlementTime);
    }

    function disable() public onlyOwner {
        inRaise = false;
        inLock = false;
        inSettlement = false;
    }
}
