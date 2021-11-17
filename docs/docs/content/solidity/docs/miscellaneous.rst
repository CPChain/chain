#############
Miscellaneous
#############


************************************
Layout of State Variables in Storage
************************************

Statically-sized variables (everything except mapping and dynamically-sized array types) are laid out contiguously in storage starting from position ``0``. Multiple items that need less than 32 bytes are packed into a single storage slot if possible, according to the following rules:

- The first item in a storage slot is stored lower-order aligned.
- Elementary types use only that many bytes that are necessary to store them.
- If an elementary type does not fit the remaining part of a storage slot, it is moved to the next storage slot.
- Structs and array data always start a new slot and occupy whole slots (but items inside a struct or array are packed tightly according to these rules).

.. warning::
    When using elements that are smaller than 32 bytes, your contract's gas usage may be higher.
    This is because the EVM operates on 32 bytes at a time. Therefore, if the element is smaller
    than that, the EVM must use more operations in order to reduce the size of the element from 32
    bytes to the desired size.

    It is only beneficial to use reduced-size arguments if you are dealing with storage values
    because the compiler will pack multiple elements into one storage slot, and thus, combine
    multiple reads or writes into a single operation. When dealing with function arguments or memory
    values, there is no inherent benefit because the compiler does not pack these values.

    Finally, in order to allow the EVM to optimize for this, ensure that you try to order your
    storage variables and ``struct`` members such that they can be packed tightly. For example,
    declaring your storage variables in the order of ``uint128, uint128, uint256`` instead of
    ``uint128, uint256, uint128``, as the former will only take up two slots of storage whereas the
    latter will take up three.

The elements of structs and arrays are stored after each other, just as if they were given explicitly.

Due to their unpredictable size, mapping and dynamically-sized array types use a Keccak-256 hash
computation to find the starting position of the value or the array data. These starting positions are always full stack slots.

The mapping or the dynamic array itself
occupies an (unfilled) slot in storage at some position ``p`` according to the above rule (or by
recursively applying this rule for mappings to mappings or arrays of arrays). For a dynamic array, this slot stores the number of elements in the array (byte arrays and strings are an exception here, see below). For a mapping, the slot is unused (but it is needed so that two equal mappings after each other will use a different hash distribution).
Array data is located at ``keccak256(p)`` and the value corresponding to a mapping key
``k`` is located at ``keccak256(k . p)`` where ``.`` is concatenation. If the value is again a
non-elementary type, the positions are found by adding an offset of ``keccak256(k . p)``.

``bytes`` and ``string`` store their data in the same slot where also the length is stored if they are short. In particular: If the data is at most ``31`` bytes long, it is stored in the higher-order bytes (left aligned) and the lowest-order byte stores ``length * 2``. If it is longer, the main slot stores ``length * 2 + 1`` and the data is stored as usual in ``keccak256(slot)``.

So for the following contract snippet::

    pragma solidity ^0.4.0;

    contract C {
      struct s { uint a; uint b; }
      uint x;
      mapping(uint => mapping(uint => s)) data;
    }

The position of ``data[4][9].b`` is at ``keccak256(uint256(9) . keccak256(uint256(4) . uint256(1))) + 1``.

.. index: memory layout

****************
Layout in Memory
****************

Solidity reserves four 32 byte slots:

- ``0x00`` - ``0x3f``: scratch space for hashing methods
- ``0x40`` - ``0x5f``: currently allocated memory size (aka. free memory pointer)
- ``0x60`` - ``0x7f``: zero slot

Scratch space can be used between statements (ie. within inline assembly). The zero slot
is used as initial value for dynamic memory arrays and should never be written to
(the free memory pointer points to ``0x80`` initially).

Solidity always places new objects at the free memory pointer and memory is never freed (this might change in the future).

.. warning::
  There are some operations in Solidity that need a temporary memory area larger than 64 bytes and therefore will not fit into the scratch space. They will be placed where the free memory points to, but given their short lifecycle, the pointer is not updated. The memory may or may not be zeroed out. Because of this, one shouldn't expect the free memory to be zeroed out.


.. index: calldata layout

*******************
Layout of Call Data
*******************

When a Solidity contract is deployed and when it is called from an
account, the input data is assumed to be in the format in :ref:`the ABI
specification <ABI>`. The ABI specification requires arguments to be padded to multiples of 32
bytes.  The internal function calls use a different convention.


.. index: variable cleanup

*********************************
Internals - Cleaning Up Variables
*********************************

When a value is shorter than 256-bit, in some cases the remaining bits
must be cleaned.
The Solidity compiler is designed to clean such remaining bits before any operations
that might be adversely affected by the potential garbage in the remaining bits.
For example, before writing a value to the memory, the remaining bits need
to be cleared because the memory contents can be used for computing
hashes or sent as the data of a message call.  Similarly, before
storing a value in the storage, the remaining bits need to be cleaned
because otherwise the garbled value can be observed.

On the other hand, we do not clean the bits if the immediately
following operation is not affected.  For instance, since any non-zero
value is considered ``true`` by ``JUMPI`` instruction, we do not clean
the boolean values before they are used as the condition for
``JUMPI``.

In addition to the design principle above, the Solidity compiler
cleans input data when it is loaded onto the stack.

Different types have different rules for cleaning up invalid values:

.. code-block:: table
	+---------------+---------------+-------------------+
	|Type           |Valid Values   |Invalid Values Mean|
	+===============+===============+===================+
	|enum of n      |0 until n - 1  |exception          |
	|members        |               |                   |
	+---------------+---------------+-------------------+
	|bool           |0 or 1         |1                  |
	+---------------+---------------+-------------------+
	|signed integers|sign-extended  |currently silently |
	|               |word           |wraps; in the      |
	|               |               |future exceptions  |
	|               |               |will be thrown     |
	|               |               |                   |
	|               |               |                   |
	+---------------+---------------+-------------------+
	|unsigned       |higher bits    |currently silently |
	|integers       |zeroed         |wraps; in the      |
	|               |               |future exceptions  |
	|               |               |will be thrown     |
	+---------------+---------------+-------------------+


*************************
Internals - The Optimizer
*************************

The Solidity optimizer operates on assembly, so it can be and also is used by other languages. It splits the sequence of instructions into basic blocks at ``JUMPs`` and ``JUMPDESTs``. Inside these blocks, the instructions are analysed and every modification to the stack, to memory or storage is recorded as an expression which consists of an instruction and a list of arguments which are essentially pointers to other expressions. The main idea is now to find expressions that are always equal (on every input) and combine them into an expression class. The optimizer first tries to find each new expression in a list of already known expressions. If this does not work, the expression is simplified according to rules like ``constant + constant = sum_of_constants`` or ``X * 1 = X``. Since this is done recursively, we can also apply the latter rule if the second factor is a more complex expression where we know that it will always evaluate to one. Modifications to storage and memory locations have to erase knowledge about storage and memory locations which are not known to be different: If we first write to location x and then to location y and both are input variables, the second could overwrite the first, so we actually do not know what is stored at x after we wrote to y. On the other hand, if a simplification of the expression x - y evaluates to a non-zero constant, we know that we can keep our knowledge about what is stored at x.

At the end of this process, we know which expressions have to be on the stack in the end and have a list of modifications to memory and storage. This information is stored together with the basic blocks and is used to link them. Furthermore, knowledge about the stack, storage and memory configuration is forwarded to the next block(s). If we know the targets of all ``JUMP`` and ``JUMPI`` instructions, we can build a complete control flow graph of the program. If there is only one target we do not know (this can happen as in principle, jump targets can be computed from inputs), we have to erase all knowledge about the input state of a block as it can be the target of the unknown ``JUMP``. If a ``JUMPI`` is found whose condition evaluates to a constant, it is transformed to an unconditional jump.

As the last step, the code in each block is completely re-generated. A dependency graph is created from the expressions on the stack at the end of the block and every operation that is not part of this graph is essentially dropped. Now code is generated that applies the modifications to memory and storage in the order they were made in the original code (dropping modifications which were found not to be needed) and finally, generates all values that are required to be on the stack in the correct place.

These steps are applied to each basic block and the newly generated code is used as replacement if it is smaller. If a basic block is split at a ``JUMPI`` and during the analysis, the condition evaluates to a constant, the ``JUMPI`` is replaced depending on the value of the constant, and thus code like

::

    var x = 7;
    data[7] = 9;
    if (data[x] != x + 2)
      return 2;
    else
      return 1;

is simplified to code which can also be compiled from

::

    data[7] = 9;
    return 1;

even though the instructions contained a jump in the beginning.


***************
Source Mappings
***************

As part of the AST output, the compiler provides the range of the source
code that is represented by the respective node in the AST. This can be
used for various purposes ranging from static analysis tools that report
errors based on the AST and debugging tools that highlight local variables
and their uses.

Furthermore, the compiler can also generate a mapping from the bytecode
to the range in the source code that generated the instruction. This is again
important for static analysis tools that operate on bytecode level and
for displaying the current position in the source code inside a debugger
or for breakpoint handling.

Both kinds of source mappings use integer indentifiers to refer to source files.
These are regular array indices into a list of source files usually called
``"sourceList"``, which is part of the combined-json and the output of
the json / npm compiler.

.. note ::
    In the case of instructions that are not associated with any particular source file,
    the source mapping assigns an integer identifier of ``-1``. This may happen for
    bytecode sections stemming from compiler-generated inline assembly statements.

The source mappings inside the AST use the following
notation:

``s:l:f``

Where ``s`` is the byte-offset to the start of the range in the source file,
``l`` is the length of the source range in bytes and ``f`` is the source
index mentioned above.

The encoding in the source mapping for the bytecode is more complicated:
It is a list of ``s:l:f:j`` separated by ``;``. Each of these
elements corresponds to an instruction, i.e. you cannot use the byte offset
but have to use the instruction offset (push instructions are longer than a single byte).
The fields ``s``, ``l`` and ``f`` are as above and ``j`` can be either
``i``, ``o`` or ``-`` signifying whether a jump instruction goes into a
function, returns from a function or is a regular jump as part of e.g. a loop.

In order to compress these source mappings especially for bytecode, the
following rules are used:

 - If a field is empty, the value of the preceding element is used.
 - If a ``:`` is missing, all following fields are considered empty.

This means the following source mappings represent the same information:

``1:2:1;1:9:1;2:1:2;2:1:2;2:1:2``

``1:2:1;:9;2:1:2;;``

***************
Tips and Tricks
***************

* Use ``delete`` on arrays to delete all its elements.
* Use shorter types for struct elements and sort them such that short types are grouped together. This can lower the gas costs as multiple ``SSTORE`` operations might be combined into a single (``SSTORE`` costs 5000 or 20000 gas, so this is what you want to optimise). Use the gas price estimator (with optimiser enabled) to check!
* Make your state variables public - the compiler will create :ref:`getters <visibility-and-getters>` for you automatically.
* If you end up checking conditions on input or state a lot at the beginning of your functions, try using :ref:`modifiers`.
* If your contract has a function called ``send`` but you want to use the built-in send-function, use ``address(contractVariable).send(amount)``.
* Initialize storage structs with a single assignment: ``x = MyStruct({a: 1, b: 2});``

.. note::
    If the storage struct has tightly packed properties, initialize it with separate assignments: ``x.a = 1; x.b = 2;``. In this way it will be easier for the optimizer to update storage in one go, thus making assignment cheaper.

**********
Cheatsheet
**********


.. _order:

Order of Precedence of Operators
================================

The following is the order of precedence for operators, listed in order of evaluation.

.. code-block:: table
	+------------+-------------------------------------+--------------------------------------------+
	| Precedence | Description                         | Operator                                   |
	+============+=====================================+============================================+
	| *1*        | Postfix increment and decrement     | ``++``, ``--``                             |
	+            +-------------------------------------+--------------------------------------------+
	|            | New expression                      | ``new <typename>``                         |
	+            +-------------------------------------+--------------------------------------------+
	|            | Array subscripting                  | ``<array>[<index>]``                       |
	+            +-------------------------------------+--------------------------------------------+
	|            | Member access                       | ``<object>.<member>``                      |
	+            +-------------------------------------+--------------------------------------------+
	|            | Function-like call                  | ``<func>(<args...>)``                      |
	+            +-------------------------------------+--------------------------------------------+
	|            | Parentheses                         | ``(<statement>)``                          |
	+------------+-------------------------------------+--------------------------------------------+
	| *2*        | Prefix increment and decrement      | ``++``, ``--``                             |
	+            +-------------------------------------+--------------------------------------------+
	|            | Unary plus and minus                | ``+``, ``-``                               |
	+            +-------------------------------------+--------------------------------------------+
	|            | Unary operations                    | ``delete``                                 |
	+            +-------------------------------------+--------------------------------------------+
	|            | Logical NOT                         | ``!``                                      |
	+            +-------------------------------------+--------------------------------------------+
	|            | Bitwise NOT                         | ``~``                                      |
	+------------+-------------------------------------+--------------------------------------------+
	| *3*        | Exponentiation                      | ``**``                                     |
	+------------+-------------------------------------+--------------------------------------------+
	| *4*        | Multiplication, division and modulo | ``*``, ``/``, ``%``                        |
	+------------+-------------------------------------+--------------------------------------------+
	| *5*        | Addition and subtraction            | ``+``, ``-``                               |
	+------------+-------------------------------------+--------------------------------------------+
	| *6*        | Bitwise shift operators             | ``<<``, ``>>``                             |
	+------------+-------------------------------------+--------------------------------------------+
	| *7*        | Bitwise AND                         | ``&``                                      |
	+------------+-------------------------------------+--------------------------------------------+
	| *8*        | Bitwise XOR                         | ``^``                                      |
	+------------+-------------------------------------+--------------------------------------------+
	| *9*        | Bitwise OR                          | ``|``                                      |
	+------------+-------------------------------------+--------------------------------------------+
	| *10*       | Inequality operators                | ``<``, ``>``, ``<=``, ``>=``               |
	+------------+-------------------------------------+--------------------------------------------+
	| *11*       | Equality operators                  | ``==``, ``!=``                             |
	+------------+-------------------------------------+--------------------------------------------+
	| *12*       | Logical AND                         | ``&&``                                     |
	+------------+-------------------------------------+--------------------------------------------+
	| *13*       | Logical OR                          | ``||``                                     |
	+------------+-------------------------------------+--------------------------------------------+
	| *14*       | Ternary operator                    | ``<conditional> ? <if-true> : <if-false>`` |
	+------------+-------------------------------------+--------------------------------------------+
	| *15*       | Assignment operators                | ``=``, ``|=``, ``^=``, ``&=``, ``<<=``,    |
	|            |                                     | ``>>=``, ``+=``, ``-=``, ``*=``, ``/=``,   |
	|            |                                     | ``%=``                                     |
	+------------+-------------------------------------+--------------------------------------------+
	| *16*       | Comma operator                      | ``,``                                      |
	+------------+-------------------------------------+--------------------------------------------+


Global Variables
================

- ``abi.encode(...) returns (bytes)``: :ref:`ABI <ABI>`-encodes the given arguments
- ``abi.encodePacked(...) returns (bytes)``: Performes :ref:`packed encoding <abi_packed_mode>` of the given arguments
- ``abi.encodeWithSelector(bytes4 selector, ...) returns (bytes)``: :ref:`ABI <ABI>`-encodes the given arguments
   starting from the second and prepends the given four-byte selector
- ``abi.encodeWithSignature(string signature, ...) returns (bytes)``: Equivalent to ``abi.encodeWithSelector(bytes4(keccak256(signature), ...)```
- ``block.blockhash(uint blockNumber) returns (bytes32)``: hash of the given block - only works for 256 most recent, excluding current, blocks - deprecated in version 0.4.22 and replaced by ``blockhash(uint blockNumber)``.
- ``block.coinbase`` (``address``): current block miner's address
- ``block.difficulty`` (``uint``): current block difficulty
- ``block.gaslimit`` (``uint``): current block gaslimit
- ``block.number`` (``uint``): current block number
- ``block.timestamp`` (``uint``): current block timestamp
- ``gasleft() returns (uint256)``: remaining gas
- ``msg.data`` (``bytes``): complete calldata
- ``msg.gas`` (``uint``): remaining gas - deprecated in version 0.4.21 and to be replaced by ``gasleft()``
- ``msg.sender`` (``address``): sender of the message (current call)
- ``msg.value`` (``uint``): number of wei sent with the message
- ``now`` (``uint``): current block timestamp (alias for ``block.timestamp``)
- ``tx.gasprice`` (``uint``): gas price of the transaction
- ``tx.origin`` (``address``): sender of the transaction (full call chain)
- ``assert(bool condition)``: abort execution and revert state changes if condition is ``false`` (use for internal error)
- ``require(bool condition)``: abort execution and revert state changes if condition is ``false`` (use for malformed input or error in external component)
- ``require(bool condition, string message)``: abort execution and revert state changes if condition is ``false`` (use for malformed input or error in external component). Also provide error message.
- ``revert()``: abort execution and revert state changes
- ``revert(string message)``: abort execution and revert state changes providing an explanatory string
- ``blockhash(uint blockNumber) returns (bytes32)``: hash of the given block - only works for 256 most recent blocks
- ``keccak256(...) returns (bytes32)``: compute the Ethereum-SHA-3 (Keccak-256) hash of the :ref:`(tightly packed) arguments <abi_packed_mode>`
- ``sha3(...) returns (bytes32)``: an alias to ``keccak256``
- ``sha256(...) returns (bytes32)``: compute the SHA-256 hash of the :ref:`(tightly packed) arguments <abi_packed_mode>`
- ``ripemd160(...) returns (bytes20)``: compute the RIPEMD-160 hash of the :ref:`(tightly packed) arguments <abi_packed_mode>`
- ``ecrecover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) returns (address)``: recover address associated with the public key from elliptic curve signature, return zero on error
- ``addmod(uint x, uint y, uint k) returns (uint)``: compute ``(x + y) % k`` where the addition is performed with arbitrary precision and does not wrap around at ``2**256``. Assert that ``k != 0`` starting from version 0.5.0.
- ``mulmod(uint x, uint y, uint k) returns (uint)``: compute ``(x * y) % k`` where the multiplication is performed with arbitrary precision and does not wrap around at ``2**256``. Assert that ``k != 0`` starting from version 0.5.0.
- ``this`` (current contract's type): the current contract, explicitly convertible to ``address``
- ``super``: the contract one level higher in the inheritance hierarchy
- ``selfdestruct(address recipient)``: destroy the current contract, sending its funds to the given address
- ``suicide(address recipient)``: a deprecated alias to ``selfdestruct``
- ``<address>.balance`` (``uint256``): balance of the :ref:`address` in Wei
- ``<address>.send(uint256 amount) returns (bool)``: send given amount of Wei to :ref:`address`, returns ``false`` on failure
- ``<address>.transfer(uint256 amount)``: send given amount of Wei to :ref:`address`, throws on failure

.. note::
    Do not rely on ``block.timestamp``, ``now`` and ``blockhash`` as a source of randomness,
    unless you know what you are doing.

    Both the timestamp and the block hash can be influenced by miners to some degree.
    Bad actors in the mining community can for example run a casino payout function on a chosen hash
    and just retry a different hash if they did not receive any money.

    The current block timestamp must be strictly larger than the timestamp of the last block,
    but the only guarantee is that it will be somewhere between the timestamps of two
    consecutive blocks in the canonical chain.

.. note::
    The block hashes are not available for all blocks for scalability reasons.
    You can only access the hashes of the most recent 256 blocks, all other
    values will be zero.


Function Visibility Specifiers
==============================

::

    function myFunction() <visibility specifier> returns (bool) {
        return true;
    }

- ``public``: visible externally and internally (creates a :ref:`getter function<getter-functions>` for storage/state variables)
- ``private``: only visible in the current contract
- ``external``: only visible externally (only for functions) - i.e. can only be message-called (via ``this.func``)
- ``internal``: only visible internally



Modifiers
=========

- ``pure`` for functions: Disallows modification or access of state - this is not enforced yet.
- ``view`` for functions: Disallows modification of state - this is not enforced yet.
- ``payable`` for functions: Allows them to receive Ether together with a call.
- ``constant`` for state variables: Disallows assignment (except initialisation), does not occupy storage slot.
- ``constant`` for functions: Same as ``view``.
- ``anonymous`` for events: Does not store event signature as topic.
- ``indexed`` for event parameters: Stores the parameter as topic.

Reserved Keywords
=================

These keywords are reserved in Solidity. They might become part of the syntax in the future:

``abstract``, ``after``, ``case``, ``catch``, ``default``, ``final``, ``in``, ``inline``, ``let``, ``match``, ``null``,
``of``, ``relocatable``, ``static``, ``switch``, ``try``, ``type``, ``typeof``.

Language Grammar
================

.. literalinclude:: grammar.txt
   :language: none
