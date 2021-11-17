
.. _contract_structure:

***********************
Structure of a Contract
***********************

Contracts in Solidity are similar to classes in object-oriented languages.
Each contract can contain declarations of :ref:`structure-state-variables`, :ref:`structure-functions`,
:ref:`structure-function-modifiers`, :ref:`structure-events`, :ref:`structure-struct-types` and :ref:`structure-enum-types`.
Furthermore, contracts can inherit from other contracts.

.. _structure-state-variables:

State Variables
===============

State variables are values which are permanently stored in contract storage.

::

    pragma solidity ^0.4.0;

    contract SimpleStorage {
        uint storedData; // State variable
        // ...
    }

See the :ref:`types` section for valid state variable types and
:ref:`visibility-and-getters` for possible choices for
visibility.

.. _structure-functions:

Functions
=========

Functions are the executable units of code within a contract.

::

    pragma solidity ^0.4.0;

    contract SimpleAuction {
        function bid() public payable { // Function
            // ...
        }
    }

:ref:`function-calls` can happen internally or externally
and have different levels of visibility (:ref:`visibility-and-getters`)
towards other contracts.

.. _structure-function-modifiers:

Function Modifiers
==================

Function modifiers can be used to amend the semantics of functions in a declarative way
(see :ref:`modifiers` in contracts section).

::

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

.. _structure-events:

Events
======

Events are convenience interfaces with the EVM logging facilities.

::

    pragma solidity ^0.4.21;

    contract SimpleAuction {
        event HighestBidIncreased(address bidder, uint amount); // Event

        function bid() public payable {
            // ...
            emit HighestBidIncreased(msg.sender, msg.value); // Triggering event
        }
    }

See :ref:`events` in contracts section for information on how events are declared
and can be used from within a dapp.

.. _structure-struct-types:

Struct Types
=============

Structs are custom defined types that can group several variables (see
:ref:`structs` in types section).

::

    pragma solidity ^0.4.0;

    contract Ballot {
        struct Voter { // Struct
            uint weight;
            bool voted;
            address delegate;
            uint vote;
        }
    }

.. _structure-enum-types:

Enum Types
==========

Enums can be used to create custom types with a finite set of 'constant values' (see
:ref:`enums` in types section).

::

    pragma solidity ^0.4.0;

    contract Purchase {
        enum State { Created, Locked, Inactive } // Enum
    }
