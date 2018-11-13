// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

// Create a private tx for node1 and node2.
// Account 1 (Party A), Account 2(Party B), Account 3(Agent P), Account 4(other party)
var account1 = "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a";
var account2 = "0xc05302acebd0730e3a18a058d7d1cb1204c4a092";
var account3 = "0xef3dd127de235f15ffb4fc0d71469d1339df6465";
var account4 = "0x3a18598184ef84198db90c28fdfdfdf56544f747";

// NOTE: you must update the public keys with the real ones in running environment.
// Party A, seller
var pubkey1 = "0x3082010a0282010100d211ba516865b11a0d6799917cbcf6653da7afa81508deb530ffd653a0d9dfcecdfda520b8c0180c8d44b904608a3939914bf4b0eccdeaa20aac9436de861c0d7c923415b82ba6a615bb8ae489a16efaa144af85f60d74800600b3766980c36fd0c9db66483c992ed8510ad860f77b2e554efd572dbd33455071568faf367b27702df0dc8aed75330d92f2897d6a4c3c69a43a6312c788584e5c63857271b941643019d4fcbbf497db68f3008829909b0f84f233972164af0f582f37a22fe4a20d047cdbd30dbab8facd24ae5ccf95f13a0bca3c061e4b35fe51b629245439a3c1132fdb5b8cfddda3823fa9da39ff1a8d052ce2759aa3f6a83c57f708ac25b10203010001"
// Party B, buyer
var pubkey2 = "0x3082010a0282010100b44e1234604ab397bf1fbb220346b6a730e0b16609e447873ea33d8d8d256f3116e39d34d8b5a094a6c82799af79f4367b21683feb9c82d707a14b34538e066af73b058caa01b39064ed39eed90b8b88593fabadd652a04ae6699aa4ee9c8a04dcefc47456c25ac165fb7f7afa173b6798471e414a3b236e5062d7c323f04344e6bd766b83250c9328a6edf04202da5be0524e398252b5cca4bb1621fd3429512717b3b5be25bd12b0e1be5d4a5d380c3c6db1498c2712e44c82bbf66da5dd9b36b5725643fc167739039eb312b6bc4d3c18ccaa5e5f4db6419fb75b286aae32dffbfec7a3db5b229e5d8ec9a0d97d96cbfb9af0ce609e9b80358884bb9306250203010001"
// Agent P, e.g. PDash
var pubkey3 = "0x3082010a0282010100c8f1e9ec5eb42d9fa72f4171b0f8c78f4a462671cef1eec52759e203c86d711f09fff31ce23b66e6dfd86c7350a13e532a45624c137040c7cfa3f0d27e07c8adce46ef031592167ce26403d555e0c6d75ea099df52204a9b3b4be6c9701ed272ba25834ec6eb440ef86209cbec2c80c26a6446a0376f4f7f367d37c3d7e3d9c83fe6b09a7843e6110667c428b5cf2de59bf0dc4d995ac4bf68258f9ef06d80a5293a4e798520b6bb563e52f67de4b5630afa3cfa3dd41e18b59cac1e7b9ac52483fa1eafc00572e9057a3a41510eae279eebaaa90d8244687b87fe77d15251418155edd3e50506d562a1176937d07096d96f86cfd7db68258496b96605fd51c30203010001"
// private tx group
var group1 = [pubkey1, pubkey2, pubkey3];

var escrowAbi = [{
    "constant": true,
    "inputs": [],
    "name": "getBalance",
    "outputs": [{"name": "", "type": "uint256"}],
    "payable": false,
    "stateMutability": "view",
    "type": "function"
}, {
    "constant": false,
    "inputs": [],
    "name": "prepay",
    "outputs": [],
    "payable": true,
    "stateMutability": "payable",
    "type": "function"
}, {
    "constant": false,
    "inputs": [{"name": "to", "type": "address"}, {"name": "value", "type": "uint256"}],
    "name": "payTo",
    "outputs": [],
    "payable": true,
    "stateMutability": "payable",
    "type": "function"
}, {"inputs": [], "payable": false, "stateMutability": "nonpayable", "type": "constructor"}, {
    "anonymous": false,
    "inputs": [{"indexed": false, "name": "_from", "type": "address"}, {
        "indexed": false,
        "name": "value",
        "type": "uint256"
    }],
    "name": "Recieve",
    "type": "event"
}, {
    "anonymous": false,
    "inputs": [{"indexed": false, "name": "to", "type": "address"}, {
        "indexed": false,
        "name": "value",
        "type": "uint256"
    }],
    "name": "PayTo",
    "type": "event"
}];
var escrowBin = '0x608060405234801561001057600080fd5b50336000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff160217905550610348806100606000396000f300608060405260043610610057576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806312065fe01461005c57806334fe1d1e146100875780637bf0862114610091575b600080fd5b34801561006857600080fd5b506100716100d1565b6040518082815260200191505060405180910390f35b61008f6100db565b005b6100cf600480360381019080803573ffffffffffffffffffffffffffffffffffffffff16906020019092919080359060200190929190505050610158565b005b6000600154905090565b346001600082825401925050819055507f6dafa44e4ef0f7a8b0488d91952b277c21e6fc0b6572aaedd63a3ebc0b74a42a3334604051808373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018281526020019250505060405180910390a1565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156101b357600080fd5b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561020e57600080fd5b600073ffffffffffffffffffffffffffffffffffffffff168273ffffffffffffffffffffffffffffffffffffffff161415151561024a57600080fd5b806001541015151561025b57600080fd5b80600154036001819055508173ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501580156102ac573d6000803e3d6000fd5b507fba9a19d1fffd67bcf0c89ea4fa1c9f02c7c6649ab43b81c9c1ade9bc8c36199a8282604051808373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018281526020019250505060405180910390a150505600a165627a7a723058201b83d778aa49736d2acf4750973fabbb463ea8b33a79da081933ebb5553d21700029'

var tradingAbi = [{
    "constant": false,
    "inputs": [{"name": "price", "type": "uint256"}],
    "name": "updateItemPrice",
    "outputs": [],
    "payable": false,
    "stateMutability": "nonpayable",
    "type": "function"
}, {
    "constant": true,
    "inputs": [],
    "name": "getItemPrice",
    "outputs": [{"name": "", "type": "uint256"}],
    "payable": false,
    "stateMutability": "view",
    "type": "function"
}, {
    "constant": false,
    "inputs": [{"name": "pubkey", "type": "string"}],
    "name": "buy",
    "outputs": [],
    "payable": false,
    "stateMutability": "nonpayable",
    "type": "function"
}, {
    "constant": true,
    "inputs": [],
    "name": "_item",
    "outputs": [{"name": "available", "type": "bool"}, {"name": "name", "type": "string"}, {
        "name": "seller",
        "type": "address"
    }, {"name": "price", "type": "uint256"}, {"name": "description", "type": "string"}],
    "payable": false,
    "stateMutability": "view",
    "type": "function"
}, {
    "constant": false,
    "inputs": [],
    "name": "confirm",
    "outputs": [],
    "payable": false,
    "stateMutability": "nonpayable",
    "type": "function"
}, {
    "constant": false,
    "inputs": [{"name": "price", "type": "uint256"}, {"name": "name", "type": "string"}, {
        "name": "description",
        "type": "string"
    }],
    "name": "setItem",
    "outputs": [],
    "payable": false,
    "stateMutability": "nonpayable",
    "type": "function"
}, {
    "constant": true,
    "inputs": [],
    "name": "_order",
    "outputs": [{"name": "available", "type": "bool"}, {"name": "price", "type": "uint256"}, {
        "name": "seller",
        "type": "address"
    }, {"name": "buyer", "type": "address"}, {"name": "pubKey", "type": "string"}],
    "payable": false,
    "stateMutability": "view",
    "type": "function"
}, {
    "constant": true,
    "inputs": [],
    "name": "getItem",
    "outputs": [{"name": "name", "type": "string"}, {"name": "price", "type": "uint256"}, {
        "name": "description",
        "type": "string"
    }],
    "payable": false,
    "stateMutability": "view",
    "type": "function"
}, {
    "constant": true,
    "inputs": [],
    "name": "_delivery",
    "outputs": [{"name": "available", "type": "bool"}, {"name": "cid", "type": "string"}, {
        "name": "symKey",
        "type": "string"
    }, {"name": "confirmed", "type": "bool"}],
    "payable": false,
    "stateMutability": "view",
    "type": "function"
}, {
    "constant": true,
    "inputs": [],
    "name": "getItemName",
    "outputs": [{"name": "", "type": "string"}],
    "payable": false,
    "stateMutability": "view",
    "type": "function"
}, {
    "constant": false,
    "inputs": [{"name": "cid", "type": "string"}, {"name": "symKey", "type": "string"}],
    "name": "deliver",
    "outputs": [],
    "payable": false,
    "stateMutability": "nonpayable",
    "type": "function"
}, {"inputs": [], "payable": false, "stateMutability": "nonpayable", "type": "constructor"}, {
    "anonymous": false,
    "inputs": [{"indexed": false, "name": "price", "type": "uint256"}, {
        "indexed": false,
        "name": "seller",
        "type": "address"
    }, {"indexed": false, "name": "buyer", "type": "address"}, {"indexed": false, "name": "pubkey", "type": "string"}],
    "name": "OrderCreated",
    "type": "event"
}, {
    "anonymous": false,
    "inputs": [{"indexed": false, "name": "cid", "type": "string"}, {
        "indexed": false,
        "name": "seller",
        "type": "address"
    }, {"indexed": false, "name": "buyer", "type": "address"}, {"indexed": false, "name": "symKey", "type": "string"}],
    "name": "ItemDelivered",
    "type": "event"
}, {
    "anonymous": false,
    "inputs": [{"indexed": false, "name": "seller", "type": "address"}, {
        "indexed": false,
        "name": "buyer",
        "type": "address"
    }],
    "name": "Confirmed",
    "type": "event"
}]
var tradingBin = '0x608060405234801561001057600080fd5b50336000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055506117c6806100606000396000f3006080604052600436106100af576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680630ae24354146100b45780632083ad82146100e1578063492cc7691461010c5780636c9231e1146101755780637022b58e146102b657806381a6ea29146102cd5780638cbac4a314610386578063c412eaba1461048e578063c814631b14610591578063c819d85a146106a3578063d6c56ac114610733575b600080fd5b3480156100c057600080fd5b506100df600480360381019080803590602001909291905050506107e2565b005b3480156100ed57600080fd5b506100f6610873565b6040518082815260200191505060405180910390f35b34801561011857600080fd5b50610173600480360381019080803590602001908201803590602001908080601f0160208091040260200160405190810160405280939291908181526020018383808284378201915050505050509192919290505050610880565b005b34801561018157600080fd5b5061018a610b5b565b6040518086151515158152602001806020018573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200184815260200180602001838103835287818151815260200191508051906020019080838360005b838110156102105780820151818401526020810190506101f5565b50505050905090810190601f16801561023d5780820380516001836020036101000a031916815260200191505b50838103825284818151815260200191508051906020019080838360005b8381101561027657808201518184015260208101905061025b565b50505050905090810190601f1680156102a35780820380516001836020036101000a031916815260200191505b5097505050505050505060405180910390f35b3480156102c257600080fd5b506102cb610cdc565b005b3480156102d957600080fd5b5061038460048036038101908080359060200190929190803590602001908201803590602001908080601f0160208091040260200160405190810160405280939291908181526020018383808284378201915050505050509192919290803590602001908201803590602001908080601f0160208091040260200160405190810160405280939291908181526020018383808284378201915050505050509192919290505050610e61565b005b34801561039257600080fd5b5061039b610f7c565b60405180861515151581526020018581526020018473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200180602001828103825283818151815260200191508051906020019080838360005b8381101561044f578082015181840152602081019050610434565b50505050905090810190601f16801561047c5780820380516001836020036101000a031916815260200191505b50965050505050505060405180910390f35b34801561049a57600080fd5b506104a3611085565b604051808060200184815260200180602001838103835286818151815260200191508051906020019080838360005b838110156104ed5780820151818401526020810190506104d2565b50505050905090810190601f16801561051a5780820380516001836020036101000a031916815260200191505b50838103825284818151815260200191508051906020019080838360005b83811015610553578082015181840152602081019050610538565b50505050905090810190601f1680156105805780820380516001836020036101000a031916815260200191505b509550505050505060405180910390f35b34801561059d57600080fd5b506105a66111dd565b6040518085151515158152602001806020018060200184151515158152602001838103835286818151815260200191508051906020019080838360005b838110156105fe5780820151818401526020810190506105e3565b50505050905090810190601f16801561062b5780820380516001836020036101000a031916815260200191505b50838103825285818151815260200191508051906020019080838360005b83811015610664578082015181840152602081019050610649565b50505050905090810190601f1680156106915780820380516001836020036101000a031916815260200191505b50965050505050505060405180910390f35b3480156106af57600080fd5b506106b8611345565b6040518080602001828103825283818151815260200191508051906020019080838360005b838110156106f85780820151818401526020810190506106dd565b50505050905090810190601f1680156107255780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34801561073f57600080fd5b506107e0600480360381019080803590602001908201803590602001908080601f0160208091040260200160405190810160405280939291908181526020018383808284378201915050505050509192919290803590602001908201803590602001908080601f01602080910402602001604051908101604052809392919081815260200183838082843782019150505050505091929192905050506113e9565b005b600160020160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561084157600080fd5b60011515600160000160009054906101000a900460ff16151514151561086657600080fd5b8060016003018190555050565b6000600160030154905090565b60001515600660000160009054906101000a900460ff1615151480156108bc575060011515600160000160009054906101000a900460ff161515145b15156108c757600080fd5b60a0604051908101604052806001151581526020016001600301548152602001600160020160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020013373ffffffffffffffffffffffffffffffffffffffff16815260200182815250600660008201518160000160006101000a81548160ff0219169083151502179055506020820151816001015560408201518160020160006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555060608201518160030160006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055506080820151816004019080519060200190610a1e9291906116f5565b509050507fe3f4f7fc5607c6ab42a1ec9a7537ede8a0731377be155565f5f20c1fa298f449600160030154600160020160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff163384604051808581526020018473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200180602001828103825283818151815260200191508051906020019080838360005b83811015610b1b578082015181840152602081019050610b00565b50505050905090810190601f168015610b485780820380516001836020036101000a031916815260200191505b509550505050505060405180910390a150565b60018060000160009054906101000a900460ff1690806001018054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610c085780601f10610bdd57610100808354040283529160200191610c08565b820191906000526020600020905b815481529060010190602001808311610beb57829003601f168201915b5050505050908060020160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1690806003015490806004018054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610cd25780601f10610ca757610100808354040283529160200191610cd2565b820191906000526020600020905b815481529060010190602001808311610cb557829003601f168201915b5050505050905085565b600660030160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16141515610d3b57600080fd5b60011515600b60000160009054906101000a900460ff161515141515610d6057600080fd5b6001600b60030160006101000a81548160ff0219169083151502179055507fe6e1c12204e969623af0187721b9bc96d35b0f7b0d41c6c61e8137869ba4a8f4600660020160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff16600660030160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff16604051808373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019250505060405180910390a1565b60001515600160000160009054906101000a900460ff161515141515610e8657600080fd5b60a0604051908101604052806001151581526020018381526020013373ffffffffffffffffffffffffffffffffffffffff16815260200184815260200182815250600160008201518160000160006101000a81548160ff0219169083151502179055506020820151816001019080519060200190610f059291906116f5565b5060408201518160020160006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff160217905550606082015181600301556080820151816004019080519060200190610f739291906116f5565b50905050505050565b60068060000160009054906101000a900460ff16908060010154908060020160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff16908060030160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1690806004018054600181600116156101000203166002900480601f01602080910402602001604051908101604052809291908181526020018280546001816001161561010002031660029004801561107b5780601f106110505761010080835404028352916020019161107b565b820191906000526020600020905b81548152906001019060200180831161105e57829003601f168201915b5050505050905085565b606060006060600180016001600301546001600401828054600181600116156101000203166002900480601f01602080910402602001604051908101604052809291908181526020018280546001816001161561010002031660029004801561112f5780601f106111045761010080835404028352916020019161112f565b820191906000526020600020905b81548152906001019060200180831161111257829003601f168201915b50505050509250808054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156111cb5780601f106111a0576101008083540402835291602001916111cb565b820191906000526020600020905b8154815290600101906020018083116111ae57829003601f168201915b50505050509050925092509250909192565b600b8060000160009054906101000a900460ff1690806001018054600181600116156101000203166002900480601f01602080910402602001604051908101604052809291908181526020018280546001816001161561010002031660029004801561128a5780601f1061125f5761010080835404028352916020019161128a565b820191906000526020600020905b81548152906001019060200180831161126d57829003601f168201915b505050505090806002018054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156113285780601f106112fd57610100808354040283529160200191611328565b820191906000526020600020905b81548152906001019060200180831161130b57829003601f168201915b5050505050908060030160009054906101000a900460ff16905084565b6060600180018054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156113df5780601f106113b4576101008083540402835291602001916113df565b820191906000526020600020905b8154815290600101906020018083116113c257829003601f168201915b5050505050905090565b600160020160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561144857600080fd5b60001515600b60000160009054906101000a900460ff161515148015611484575060011515600660000160009054906101000a900460ff161515145b151561148f57600080fd5b60806040519081016040528060011515815260200183815260200182815260200160001515815250600b60008201518160000160006101000a81548160ff02191690831515021790555060208201518160010190805190602001906114f59291906116f5565b5060408201518160020190805190602001906115129291906116f5565b5060608201518160030160006101000a81548160ff0219169083151502179055509050507f5d5f7a595ba2e0dbe03f6c3761f5de07df55511cc6640f71a613718a1729ddad82600660020160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff16600660030160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff168460405180806020018573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200180602001838103835287818151815260200191508051906020019080838360005b8381101561164d578082015181840152602081019050611632565b50505050905090810190601f16801561167a5780820380516001836020036101000a031916815260200191505b50838103825284818151815260200191508051906020019080838360005b838110156116b3578082015181840152602081019050611698565b50505050905090810190601f1680156116e05780820380516001836020036101000a031916815260200191505b50965050505050505060405180910390a15050565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061173657805160ff1916838001178555611764565b82800160010185558215611764579182015b82811115611763578251825591602001919060010190611748565b5b5090506117719190611775565b5090565b61179791905b8082111561179357600081600090555060010161177b565b5090565b905600a165627a7a7230582011538498784cd545e8b90c2ea566f28e206c0332a9c2a6cc0f61ee4727cfaa2e0029';

var global = {
    tradingContractAddr: '0x4f8447b19cc84ef7c906a378678bb6a157227d30',
    escrowContractAddr: '0xF1c2E522e1De308B7348E8A8Ec4CC3C519e60Af8'
};

var GWEI = Math.pow(10, 9)

if (typeof Scene == 'undefined') {
    Scene = 1;
}

var getTradingContractInst = function () {
    var contractAddr = global['tradingContractAddr'];
    var tradingContract = web3.eth.contract(tradingAbi);
    return tradingContract.at(contractAddr);
};

var getEscrowContractInst = function () {
    var contractAddr = global['escrowContractAddr'];
    var escrowContract = web3.eth.contract(escrowAbi);
    return escrowContract.at(contractAddr);
}

var scenes = {
    // (run on node 3)Agent P deploys a trading contract CT involving party A and party B on private
    1: function () {

        var tradingContract = web3.eth.contract(tradingAbi)
        web3.eth.defaultAccount = account3;
        tradingContract.new(
            "Trading Contract",
            {
                from: account3,
                data: tradingBin,
                gas: 3000000,
                isPrivate: true,
                participants: group1
            }, function (e, contract) {
                console.info('Trading contract CT created, address: ' + contract.address + ' , transactionHash: ' + contract.transactionHash);
                admin.sleep(2) // wait for a moment
                global['tradingContractAddr'] = eth.getTransactionReceipt(contract.transactionHash).contractAddress
                console.log('tradingContractAddr = ' + global['tradingContractAddr'])
            });
        admin.sleep(5) // wait for a moment
    },
    // (run on node 3)Agent P deploys an escrow contract CE on public
    2: function () {
        var escrowContract = web3.eth.contract(escrowAbi);
        web3.eth.defaultAccount = account3;
        escrowContract.new(
            "Escrow Contract",
            {
                from: account3,
                data: escrowBin,
                gas: 1000000,
                isPrivate: false
            }, function (e, contract) {
                console.info('Escrow contract CE created, address: ' + contract.address + ' , transactionHash: ' + contract.transactionHash);
                admin.sleep(2); // wait for a momentsde
                global['escrowContractAddr'] = eth.getTransactionReceipt(contract.transactionHash).contractAddress;
                console.log('escrowContractAddr = ' + global['escrowContractAddr']);
            });
        admin.sleep(5)
    },
    // (run on node 1)Party A sets the item for sale
    3: function () {
        web3.eth.defaultAccount = account1;
        var tradingContractInst = getTradingContractInst();
        var result = tradingContractInst.setItem.sendTransaction(120000000 * GWEI, "A secret data", "You may want to get it!", {
            gas: 3000000,
            isPrivate: true,
            participants: group1
        });
        console.log("setItem() result: " + result);
    },
    // (run on node 2)Party B pays money to the escrow contract CE
    4: function () {
        web3.eth.defaultAccount = account2;

        // Gets the item for sale.
        var tradingContractInst = getTradingContractInst();
        var itemName = tradingContractInst.getItemName.call({isPrivate: true, participants: group1});
        var itemPrice = tradingContractInst.getItemPrice.call({isPrivate: true, participants: group1});
        console.log("Item: (" + itemName + "," + itemPrice + ")");

        var escrowContractInst = getEscrowContractInst();
        var result = escrowContractInst.prepay.sendTransaction({
            gas: 200000,
            isPrivate: false,
            value: 120000000 * GWEI
        });
        console.log("prepay() result: " + result);

        var result = escrowContractInst.getBalance.call({
            gas: 200000,
            isPrivate: false
        });
        console.log("getBalance() result: " + result);
    },
    // (run on node2)Party B then sends contract CT an order
    5: function () {
        web3.eth.defaultAccount = account2;

        var tradingContractInst = getTradingContractInst();
        var result = tradingContractInst.buy.sendTransaction(pubkey2, {
            gas: 3000000,
            isPrivate: true,
            participants: group1
        });
        console.log("buy() result: " + result);
        console.log("the order is: " + tradingContractInst._order({isPrivate: true}));
    },
    // (run on node1)Party A sends the delivery message attached with the symmetric key encrypted by the buyer's public key
    6: function () {
        web3.eth.defaultAccount = account1;

        var tradingContractInst = getTradingContractInst();
        var result = tradingContractInst.deliver.sendTransaction("cid1", "symmetric-key-encrypted-by-pubkey", {
            gas: 3000000,
            isPrivate: true,
            participants: group1
        });
        console.log("deliver() result: " + result);
        console.log("the delivery is: " + tradingContractInst._delivery({isPrivate: true}));
    },
    // (run on node2)Party B receives the delivery and send confirmation message
    7: function () {
        web3.eth.defaultAccount = account2;

        var tradingContractInst = getTradingContractInst();
        var result = tradingContractInst.confirm({
            gas: 3000000,
            isPrivate: true,
            participants: group1
        });
        console.log("confirm() result: " + result);
        console.log("the delivery is: " + tradingContractInst._delivery({isPrivate: true}));
    },
    // (run on node3)Agent P notice the confirmation and transfer money to Party A
    8: function () {
        web3.eth.defaultAccount = account3;

        var tradingContractInst = getTradingContractInst();
        var fee = tradingContractInst.getItemPrice({isPrivate: true});

        var escrowContractInst = getEscrowContractInst();
        var result = escrowContractInst.payTo(account1, fee, {gas: 200000});
        console.log("payTo() result: " + result);

        var result = escrowContractInst.getBalance.call({gas: 200000});
        console.log("getBalance() result: " + result);
    },
    // (run on node4)Other parties could not get any information about the transaction between A and B
    9: function () {
        web3.eth.defaultAccount = account4;

        var tradingContractInst = getTradingContractInst();
        var itemName = tradingContractInst.getItemName({isPrivate: true});
        console.log("Inspect the trading, got: " + itemName)
    },
}

console.info("Scene<" + Scene + "> begins.");
scenes[Scene]();
console.info("Scene<" + Scene + "> ends.");
