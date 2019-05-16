/**
* only 5 config parameters work in this contract
* other parts are not used
**/


pragma solidity ^0.4.24;


contract Rpt {
    // The 5 weight configs.
    uint public alpha = 50;
    uint public beta = 15;
    uint public gamma = 10;
    uint public psi = 15;
    uint public omega = 10;
    
    // other configs.
    uint public window = 4; // number of blocks used for rpt calculation

    uint public randomLevel = 5; // 0 - 10

    address public owner;
    
    modifier onlyOwner() {require(msg.sender == owner);_;}
    
    event UpdateConfigs(uint blockNumber);
    event UpdateOneConfig(uint blockNumber, string configName, uint configValue);
    
    
    constructor() public {
        owner = msg.sender;
    }

    
    /** modified all configs. */
    function updateConfigs(
        uint _alpha, 
        uint _beta, 
        uint _gamma, 
        uint _psi, 
        uint _omega,
        uint _window,
        uint _randomLevel
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
            randomLevel = _randomLevel;

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

    function updateRandomLevel(uint _randomLevel) public onlyOwner {
        randomLevel = _randomLevel;
        emit UpdateOneConfig(block.number, "randomLevel", randomLevel);
    }
}