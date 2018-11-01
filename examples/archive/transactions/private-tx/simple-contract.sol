pragma solidity ^0.4.21;

contract Gossip {
    string message;

    constructor(string _msg) public {
        message = _msg;
    }

    function getMsg() view public returns(string) {
        return message;
    }

    function setMsg(string _msg) public {
        message = _msg;
    }
}