pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract Reward {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner;

    // data structure for investors
    Set.Data private enodes;
    mapping(address => uint256) public investments;
    mapping(uint256 => mapping(address => bool)) returned; // record investors who have claimed interests for each round
    uint256 public totalInvestment;
    uint256 public totalInterest;


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
        bonusPool = bonusPool.sub(totalInterest);
        totalInvestment = totalInvestment.add(totalInterest);
        totalInterest = 0;
        assert(totalInvestment.add(bonusPool) == address(this).balance);
        emit SetTime("next lock time", nextLockTime);
        emit NewRaise(now);
    }

    // fund bonus pool
    function () public payable duringRaise {
        bonusPool = bonusPool.add(msg.value);
        emit FundBonusPool(msg.sender, msg.value, bonusPool);
    }

    // investors can only submit deposit during raise
    function deposit() public payable duringRaise {
        investments[msg.sender] = investments[msg.sender].add(msg.value);
        totalInvestment = totalInvestment.add(msg.value);
        emit AddInvestment(msg.sender, msg.value, totalInvestment);
        if(investments[msg.sender] >= enodeThreshold) {
            enodes.insert(msg.sender);
            emit NewEnode(msg.sender, investments[msg.sender]);
        }
        assert(totalInvestment.add(bonusPool) == address(this).balance);
    }

    // investors can only withdraw during raise
    function withdraw(uint amount) public duringRaise {
        require(amount <= investments[msg.sender]);
        msg.sender.transfer(amount);
        investments[msg.sender] = investments[msg.sender].sub(amount);
        totalInvestment = totalInvestment.sub(amount);
        emit SubInvestment(msg.sender, amount, totalInvestment);
        if(investments[msg.sender] < enodeThreshold) {
            enodes.remove(msg.sender);
            emit EnodeQuit(msg.sender, investments[msg.sender]);
        }
        assert(totalInvestment.add(bonusPool) == address(this).balance);
    }

    // start a new lock period
    function newLock() public onlyOwner {
        require(now >= nextLockTime.sub(1 days));
        inRaise = false;
        inLock = true;
        inSettlement = false;
        nextSettlementTime = now.add(lockPeriod);
        emit SetTime("next settlement time", nextSettlementTime);
        emit NewLock(now);
    }

    // start a new settlement
    function newSettlement() public onlyOwner {
        require(now >= nextSettlementTime.sub(1 days));
        inRaise = false;
        inLock = false;
        inSettlement = true;
        nextRaiseTime = now.add(settlementPeriod);
        emit SetTime("next raise time", nextRaiseTime);
        emit NewSettlement(now);
    }

    // calculate interest
    function settle(address investor) internal {
        require(!returned[round][investor]);
        require(enodes.contains(investor));
        uint256 interest;
        interest = bonusPool.mul(investments[investor]).div(totalInvestment);
        totalInterest = totalInterest.add(interest);
        investments[investor] = investments[investor].add(interest);
        returned[round][investor] = true;
        emit ApplyForSettlement(investor, interest);
    }

    // investors can only claim interest during settlement
    function claimInterest() public duringSettlement {
        settle(msg.sender);
    }

    // owner will distribute interest to those who do not claim
    function distributeInterest(address investor) public onlyOwner duringSettlement {
        settle(investor);
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

    // refund money to investor
    function refund(address investor, uint256 amount) public onlyOwner {
        require(investments[investor] >= amount);
        investor.transfer(amount);
        investments[investor] = investments[investor].sub(amount);
        if(investments[investor] < enodeThreshold) {
            enodes.remove(investor);
            emit EnodeQuit(investor, investments[investor]);
        }
    }

    function disable() public onlyOwner {
        inRaise = false;
        inLock = false;
        inSettlement = false;
    }
}
