pragma solidity ^0.4.24;

contract ProposerRegister {

    address owner;

    mapping(address => bytes) public _validatorPublicKeys;

    struct EncryptedNodeInfo {
        // validator's address ==> proposer's node info encrypted with validator's public key
        mapping(address => bytes) nodeInfosEncryptedByValidator;
    }

    struct NodeInfoInTerm {
        // proposer's address ==> proposer's encrypted node infos encrypted by validators' public key
        mapping(address => EncryptedNodeInfo) encryptedNodeInfosOfProposer;
    }

    mapping(uint => NodeInfoInTerm) _nodeInfoInTerm;

    // ------------------------------------------------------------------
    constructor () public {
        owner = msg.sender;
    }

    function registerPublicKey(bytes memory rsaPublicKey) public payable {
        _validatorPublicKeys[msg.sender] = rsaPublicKey;
    }

    function getPublicKey(address addr) public view returns (bytes memory){
        return _validatorPublicKeys[addr];
    }

    function addNodeInfo(uint term, address validator, bytes memory encrpytedNodeInfo) public payable {
        address proposer = msg.sender;
        _nodeInfoInTerm[term].encryptedNodeInfosOfProposer[proposer].nodeInfosEncryptedByValidator[validator] = encrpytedNodeInfo;
    }

    function getNodeInfo(uint term, address proposer) public view returns (bytes memory) {
        address validator = msg.sender;
        return _nodeInfoInTerm[term].encryptedNodeInfosOfProposer[proposer].nodeInfosEncryptedByValidator[validator];
    }
}