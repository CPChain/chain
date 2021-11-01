Structure of a Contract
=======================

Contracts in Solidity are similar to classes in object-oriented
languages. Each contract can contain declarations of
structure-state-variables, structure-functions,
structure-function-modifiers, structure-events, structure-struct-types
and structure-enum-types. Furthermore, contracts can inherit from other
contracts.

State Variables
---------------

State variables are values which are permanently stored in contract
storage.

    pragma solidity ^0.4.0;

    contract SimpleStorage {
        uint storedData; // State variable
        // ...
    }

See the types section for valid state variable types and
visibility-and-getters for possible choices for visibility.

Functions
---------

Functions are the executable units of code within a contract.

    pragma solidity ^0.4.0;

    contract SimpleAuction {
        function bid() public payable { // Function
            // ...
        }
    }

function-calls can happen internally or externally and have different
levels of visibility (visibility-and-getters) towards other contracts.

Function Modifiers
------------------

Function modifiers can be used to amend the semantics of functions in a
declarative way (see modifiers in contracts section).

    pragma solidity ^0.4.22;

    contract Purchase {
        address public seller;

        modifier onlySeller() { // Modifier
            require(
                msg.sender == seller,
                "Only seller can call this."
            );
            _;
        }

        function abort() public onlySeller { // Modifier usage
            // ...
        }
    }

Events
------

Events are convenience interfaces with the EVM logging facilities.

    pragma solidity ^0.4.21;

    contract SimpleAuction {
        event HighestBidIncreased(address bidder, uint amount); // Event

        function bid() public payable {
            // ...
            emit HighestBidIncreased(msg.sender, msg.value); // Triggering event
        }
    }

See events in contracts section for information on how events are
declared and can be used from within a dapp.

Struct Types
------------

Structs are custom defined types that can group several variables (see
structs in types section).

    pragma solidity ^0.4.0;

    contract Ballot {
        struct Voter { // Struct
            uint weight;
            bool voted;
            address delegate;
            uint vote;
        }
    }

Enum Types
----------

Enums can be used to create custom types with a finite set of 'constant
values' (see enums in types section).

    pragma solidity ^0.4.0;

    contract Purchase {
        enum State { Created, Locked, Inactive } // Enum
    }
