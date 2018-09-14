pragma solidity ^0.4.11;

contract SignerConnectionRegister {

    address owner;

    // register public key: address -> bytes rsaPublicKey
    mapping(address => bytes) public _publicKeys;

    struct EncryptedNode {
        // other committee's address,used as encryptedNodes.keys
        // address[] otherAddresses;

        // other committee's -> encryptedNodeInfo;
        mapping(address => bytes) encryptedNodes;
    }

    struct NodeInfoInView {
        // RSA public key owner address => encrypted nodeInfo by others
        mapping(address => EncryptedNode) encryptedNodes;
    }

    // NodeInfoInView in each view:viewIndex -> NodeInfoInView
    mapping(uint => NodeInfoInView) _nodeInfoInViews;

    // ------------------------------------------------------------------
    constructor () public {
        owner = msg.sender;
    }

    function registerPublicKey(bytes memory rsaPublicKey) public payable {
        _publicKeys[msg.sender] = rsaPublicKey;
    }

    function getPublicKey(address addr) public view returns (bytes memory){
        return _publicKeys[addr];
    }

    function addNodeInfo(uint viewIndex, address otherAddress, bytes memory encrpytedNodeInfo) public payable {
        // _nodeInfoInViews[viewIndex].encryptedNodes[msg.sender].otherAddresses.push(otherAddress);
        _nodeInfoInViews[viewIndex].encryptedNodes[msg.sender].encryptedNodes[otherAddress] = encrpytedNodeInfo;
    }

    // return msg.sender's node info in some view that encrypted by other's rsaPublicKey
    function getNodeInfo(uint viewIndex, address otherAddress) public view returns (bytes memory) {
        return _nodeInfoInViews[viewIndex].encryptedNodes[msg.sender].encryptedNodes[otherAddress];
    }
}