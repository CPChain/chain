pragma solidity ^0.4.24;

/** @title Reputation calculate */

import "./lib/safeMath.sol";
import "./primitives/primitive_contracts.sol";

contract Rpt {
    using PrimitiveContractsInterface for address;
    using SafeMath for uint256;
    // The 5 weight configs.
    uint public alpha = 50;
    uint public beta = 15;
    uint public gamma = 10;
    uint public psi = 15;
    uint public omega = 10;
    
    // other configs.
    uint public window = 4;
    // candidate per round
    uint public f = 21;
    
    address public owner;
    
    modifier onlyOwner() {require(msg.sender == owner);_;}
    
    // logs when owner changed cpnfigs or expr. 
    event UpdateConfigs(uint blockNumber);
    event UpdateOneConfig(uint blockNumber, string configName, uint configValue);
    event SetExp(uint blockNumber, string exprNmae, string expr);

    
    
    constructor() public {
        owner = msg.sender;
    }
    
    // function setPCAddr(address _addr) public onlyOwner {
    //     PC = PrimitiveContractsInterface(_addr);
    // }
    
    /** modified all configs. */
    function updateConfigs(
        uint _alpha, 
        uint _beta, 
        uint _gamma, 
        uint _psi, 
        uint _omega, 
        uint _f, 
        uint _window
        ) 
        public 
        onlyOwner()
        {
            alpha = _alpha;
            beta = _beta;
            gamma = _gamma;
            psi = _psi;
            omega = _omega;
            window = _window;
            f = _f;
            
            emit UpdateConfigs(block.number);
        }
    
    /** modified one config. */
    function updateAlpha(uint _alpha) public onlyOwner(){
        alpha = _alpha;
        emit UpdateOneConfig(block.number, "alpha", alpha);
    }
    
    function updateBeta(uint _beta) public onlyOwner() {
        beta = _beta;
        emit UpdateOneConfig(block.number, "beta", beta);
    }
    
    function updateGamma(uint _gamma) public onlyOwner() {
        gamma = _gamma;
        emit UpdateOneConfig(block.number, "gamma", gamma);
    }
    
    function updatePsi(uint _psi) public onlyOwner() {
        psi = _psi;
        emit UpdateOneConfig(block.number, "psi", psi);
    }
    
    function updateOmega(uint _omega) public onlyOwner() {
        omega = _omega;
        emit UpdateOneConfig(block.number, "omega", omega);
    }
    
    function updateWindow(uint _window) public onlyOwner() {
        window = _window;
        emit UpdateOneConfig(block.number, "window", window);
    }
    
    function getRpt(address _addr, uint _blockNumber) public view returns (uint rpt){
        require(_blockNumber <= block.number, "blockNumber is too large.");
        rpt = 0;
        /*
        if(3 == _addr.getMaintenance(_blockNumber)) {
            return rpt;
        }
        */
        rpt = rpt.add(alpha * getCoinage(_addr, _blockNumber));
        rpt = rpt.add(beta * getTx(_addr, _blockNumber));
        rpt = rpt.add(gamma * getProxyRep(_addr, _blockNumber));
        rpt = rpt.add(psi * getDataContribution(_addr, _blockNumber));
        rpt = rpt.add(omega * getBlockchainMaintenance(_addr, _blockNumber));
        return rpt;
    }
    
    function getCoinage(address _addr, uint _blockNumber) public view returns(uint) {
        uint rank = _addr.getRank(_blockNumber);
        if (rank < 2) return 100;
        if (rank < 5) return 90;
        if (rank < 15) return 80;
        if (rank < 35) return 70;
        if (rank < 60) return 60;
        if (rank < 80) return 40;
        return rank;
    }
    
    function getTx(address _addr, uint _blockNumber) public view returns(uint) {
        uint txAmount = _addr.getTxVolume(_blockNumber);
        txAmount = txAmount.mul(5);
        if(txAmount > 100) return 100;
        return txAmount;
    }
    
    function getProxyRep(address _addr, uint _blockNumber) public view returns(uint) {
        uint isProxy = _addr.isProxy(_blockNumber);
        if (isProxy == 0) {
            return 0;
        }
        uint txAmount;
        uint res;
        txAmount = _addr.getProxyCount(_blockNumber);
        res = txAmount.mul(5).add(10);
        if(res > 100) return 100;
        return res;
    }
    
    function getDataContribution(address _addr, uint _blockNumber) public view returns(uint) {
        uint uploadNum;
        uint res;
        uploadNum = _addr.getUploadInfo(_blockNumber);
        res = uploadNum.mul(3);
        if(res > 100) return 100;
        return res;
    }
    
    function getBlockchainMaintenance(address _addr, uint _blockNumber) public view returns(uint) {
        //return 20;
        ///*
        uint node = _addr.getMaintenance(_blockNumber);
        if (node == 0) return 100;
        if (node == 1) return 80;
        return 60;
        //*/
    }
}
