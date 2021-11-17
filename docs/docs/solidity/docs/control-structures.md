# Expressions and Control Structures

## Input Parameters and Output Parameters

As in Javascript, functions may take parameters as input; unlike in
Javascript and C, they may also return arbitrary number of parameters as
output.

### Input Parameters

The input parameters are declared the same way as variables are. As an
exception, unused parameters can omit the variable name. For example,
suppose we want our contract to accept one kind of external calls with
two integers, we would write something like:

    pragma solidity ^0.4.16;

    contract Simple {
        function taker(uint _a, uint _b) public pure {
            // do something with _a and _b.
        }
    }

### Output Parameters

The output parameters can be declared with the same syntax after the
`returns` keyword. For example, suppose we wished to return two results:
the sum and the product of the two given integers, then we would write:

    pragma solidity ^0.4.16;

    contract Simple {
        function arithmetics(uint _a, uint _b)
            public
            pure
            returns (uint o_sum, uint o_product)
        {
            o_sum = _a + _b;
            o_product = _a * _b;
        }
    }

The names of output parameters can be omitted. The output values can
also be specified using `return` statements. The `return` statements are
also capable of returning multiple values, see
[Returning Multiple Values](#returning-multiple-values). Return parameters are
initialized to zero; if they are not explicitly set, they stay to be
zero.

Input parameters and output parameters can be used as expressions in the
function body. There, they are also usable in the left-hand side of
assignment.

## Control Structures

Most of the control structures from JavaScript are available in Solidity
except for `switch` and `goto`. So there is: `if`, `else`, `while`,
`do`, `for`, `break`, `continue`, `return`, `? :`, with the usual
semantics known from C or JavaScript.

Parentheses can *not* be omitted for conditionals, but curly brances can
be omitted around single-statement bodies.

Note that there is no type conversion from non-boolean to boolean types
as there is in C and JavaScript, so `if (1) { ... }` is *not* valid
Solidity.

### Returning Multiple Values 

When a function has multiple output parameters,
`return (v0, v1, ..., vn)` can return multiple values. The number of
components must be the same as the number of output parameters.

## Function Calls

### Internal Function Calls

Functions of the current contract can be called directly ("internally"),
also recursively, as seen in this nonsensical example:

    pragma solidity ^0.4.16;

    contract C {
        function g(uint a) public pure returns (uint ret) { return f(); }
        function f() internal pure returns (uint ret) { return g(7) + f(); }
    }

These function calls are translated into simple jumps inside the EVM.
This has the effect that the current memory is not cleared, i.e. passing
memory references to internally-called functions is very efficient. Only
functions of the same contract can be called internally.

### External Function Calls

The expressions `this.g(8);` and `c.g(2);` (where `c` is a contract
instance) are also valid function calls, but this time, the function
will be called "externally", via a message call and not directly via
jumps. Please note that function calls on `this` cannot be used in the
constructor, as the actual contract has not been created yet.

Functions of other contracts have to be called externally. For an
external call, all function arguments have to be copied to memory.

When calling functions of other contracts, the amount of Wei sent with
the call and the gas can be specified with special options `.value()`
and `.gas()`, respectively:

    pragma solidity ^0.4.0;

    contract InfoFeed {
        function info() public payable returns (uint ret) { return 42; }
    }

    contract Consumer {
        InfoFeed feed;
        function setFeed(address addr) public { feed = InfoFeed(addr); }
        function callFeed() public { feed.info.value(10).gas(800)(); }
    }

The modifier `payable` has to be used for `info`, because otherwise, the
[.value()]{.title-ref} option would not be available.

Note that the expression `InfoFeed(addr)` performs an explicit type
conversion stating that "we know that the type of the contract at the
given address is `InfoFeed`" and this does not execute a constructor.
Explicit type conversions have to be handled with extreme caution. Never
call a function on a contract where you are not sure about its type.

We could also have used
`function setFeed(InfoFeed _feed) { feed = _feed; }` directly. Be
careful about the fact that `feed.info.value(10).gas(800)` only
(locally) sets the value and amount of gas sent with the function call
and only the parentheses at the end perform the actual call.

Function calls cause exceptions if the called contract does not exist
(in the sense that the account does not contain code) or if the called
contract itself throws an exception or goes out of gas.

::: warning

Any interaction with another contract imposes a potential danger,
especially if the source code of the contract is not known in advance.
The current contract hands over control to the called contract and that
may potentially do just about anything. Even if the called contract
inherits from a known parent contract, the inheriting contract is only
required to have a correct interface. The implementation of the
contract, however, can be completely arbitrary and thus, pose a danger.
In addition, be prepared in case it calls into other contracts of your
system or even back into the calling contract before the first call
returns. This means that the called contract can change state variables
of the calling contract via its functions. Write your functions in a way
that, for example, calls to external functions happen after any changes
to state variables in your contract so your contract is not vulnerable
to a reentrancy exploit.
:::

### Named Calls and Anonymous Function Parameters

Function call arguments can also be given by name, in any order, if they
are enclosed in `{ }` as can be seen in the following example. The
argument list has to coincide by name with the list of parameters from
the function declaration, but can be in arbitrary order.

    pragma solidity ^0.4.0;

    contract C {
        function f(uint key, uint value) public {
            // ...
        }

        function g() public {
            // named arguments
            f({value: 2, key: 3});
        }
    }

### Omitted Function Parameter Names

The names of unused parameters (especially return parameters) can be
omitted. Those parameters will still be present on the stack, but they
are inaccessible.

    pragma solidity ^0.4.16;

    contract C {
        // omitted name for parameter
        function func(uint k, uint) public pure returns(uint) {
            return k;
        }
    }

## Creating Contracts via `new` 

A contract can create a new contract using the `new` keyword. The full
code of the contract being created has to be known in advance, so
recursive creation-dependencies are not possible.

    pragma solidity ^0.4.0;

    contract D {
        uint x;
        function D(uint a) public payable {
            x = a;
        }
    }

    contract C {
        D d = new D(4); // will be executed as part of C's constructor

        function createD(uint arg) public {
            D newD = new D(arg);
        }

        function createAndEndowD(uint arg, uint amount) public payable {
            // Send ether along with the creation
            D newD = (new D).value(amount)(arg);
        }
    }

As seen in the example, it is possible to forward Ether while creating
an instance of `D` using the `.value()` option, but it is not possible
to limit the amount of gas. If the creation fails (due to out-of-stack,
not enough balance or other problems), an exception is thrown.

## Order of Evaluation of Expressions

The evaluation order of expressions is not specified (more formally, the
order in which the children of one node in the expression tree are
evaluated is not specified, but they are of course evaluated before the
node itself). It is only guaranteed that statements are executed in
order and short-circuiting for boolean expressions is done. See
[Order of Precedence of Operators](./miscellaneous.md#order-of-precedence-of-operators) for more information.

## Assignment

### Destructuring Assignments and Returning Multiple Values

Solidity internally allows tuple types, i.e. a list of objects of
potentially different types whose size is a constant at compile-time.
Those tuples can be used to return multiple values at the same time.
These can then either be assigned to newly declared variables or to
pre-existing variables (or LValues in general):

    pragma solidity >0.4.23 <0.5.0;

    contract C {
        uint[] data;

        function f() public pure returns (uint, bool, uint) {
            return (7, true, 2);
        }

        function g() public {
            // Variables declared with type and assigned from the returned tuple.
            (uint x, bool b, uint y) = f();
            // Common trick to swap values -- does not work for non-value storage types.
            (x, y) = (y, x);
            // Components can be left out (also for variable declarations).
            (data.length,,) = f(); // Sets the length to 7
            // Components can only be left out at the left-hand-side of assignments, with
            // one exception:
            (x,) = (1,);
            // (1,) is the only way to specify a 1-component tuple, because (1) is
            // equivalent to 1.
        }
    }

::: tip

Prior to version 0.4.24 it was possible to assign to tuples of smaller
size, either filling up on the left or on the right side (which ever was
empty). This is now deprecated, both sides have to have the same number
of components.
:::

### Complications for Arrays and Structs

The semantics of assignment are a bit more complicated for non-value
types like arrays and structs. Assigning *to* a state variable always
creates an independent copy. On the other hand, assigning to a local
variable creates an independent copy only for elementary types, i.e.
static types that fit into 32 bytes. If structs or arrays (including
`bytes` and `string`) are assigned from a state variable to a local
variable, the local variable holds a reference to the original state
variable. A second assignment to the local variable does not modify the
state but only changes the reference. Assignments to members (or
elements) of the local variable *do* change the state.

## Scoping and Declarations 

A variable which is declared will have an initial default value whose
byte-representation is all zeros. The "default values" of variables are
the typical "zero-state" of whatever the type is. For example, the
default value for a `bool` is `false`. The default value for the `uint`
or `int` types is `0`. For statically-sized arrays and `bytes1` to
`bytes32`, each individual element will be initialized to the default
value corresponding to its type. Finally, for dynamically-sized arrays,
`bytes` and `string`, the default value is an empty array or string.

A variable declared anywhere within a function will be in scope for the
*entire function*, regardless of where it is declared (this will change
soon, see below). This happens because Solidity inherits its scoping
rules from JavaScript. This is in contrast to many languages where
variables are only scoped where they are declared until the end of the
semantic block. As a result, the following code is illegal and cause the
compiler to throw an error, `Identifier already declared`:

    // This will not compile

    pragma solidity ^0.4.16;

    contract ScopingErrors {
        function scoping() public {
            uint i = 0;

            while (i++ < 1) {
                uint same1 = 0;
            }

            while (i++ < 2) {
                uint same1 = 0;// Illegal, second declaration of same1
            }
        }

        function minimalScoping() public {
            {
                uint same2 = 0;
            }

            {
                uint same2 = 0;// Illegal, second declaration of same2
            }
        }

        function forLoopScoping() public {
            for (uint same3 = 0; same3 < 1; same3++) {
            }

            for (uint same3 = 0; same3 < 1; same3++) {// Illegal, second declaration of same3
            }
        }
    }

In addition to this, if a variable is declared, it will be initialized
at the beginning of the function to its default value. As a result, the
following code is legal, despite being poorly written:

    pragma solidity ^0.4.0;

    contract C {
        function foo() public pure returns (uint) {
            // baz is implicitly initialized as 0
            uint bar = 5;
            if (true) {
                bar += baz;
            } else {
                uint baz = 10;// never executes
            }
            return bar;// returns 5
        }
    }

### Scoping starting from Version 0.5.0 

Starting from version 0.5.0, Solidity will change to the more widespread
scoping rules of C99 (and many other languages): Variables are visible
from the point right after their declaration until the end of a
`{ }`-block. As an exception to this rule, variables declared in the
initialization part of a for-loop are only visible until the end of the
for-loop.

Variables and other items declared outside of a code block, for example
functions, contracts, user-defined types, etc., do not change their
scoping behaviour. This means you can use state variables before they
are declared and call functions recursively.

These rules are already introduced now as an experimental feature.

As a consequence, the following examples will compile without warnings,
since the two variables have the same name but disjoint scopes. In
non-0.5.0-mode, they have the same scope (the function `minimalScoping`)
and thus it does not compile there.

    pragma solidity ^0.4.0;
    pragma experimental "v0.5.0";
    contract C {
        function minimalScoping() pure public {
            {
                uint same2 = 0;
            }

            {
                uint same2 = 0;
            }
        }
    }

As a special example of the C99 scoping rules, note that in the
following, the first assignment to `x` will actually assign the outer
and not the inner variable. In any case, you will get a warning about
the outer variable being shadowed.

    pragma solidity ^0.4.0;
    pragma experimental "v0.5.0";
    contract C {
        function f() pure public returns (uint) {
            uint x = 1;
            {
                x = 2; // this will assign to the outer variable
                uint x;
            }
            return x; // x has value 2
        }
    }

## Error handling: Assert, Require, Revert and Exceptions

Solidity uses state-reverting exceptions to handle errors. Such an
exception will undo all changes made to the state in the current call
(and all its sub-calls) and also flag an error to the caller. The
convenience functions `assert` and `require` can be used to check for
conditions and throw an exception if the condition is not met. The
`assert` function should only be used to test for internal errors, and
to check invariants. The `require` function should be used to ensure
valid conditions, such as inputs, or contract state variables are met,
or to validate return values from calls to external contracts. If used
properly, analysis tools can evaluate your contract to identify the
conditions and function calls which will reach a failing `assert`.
Properly functioning code should never reach a failing assert statement;
if this happens there is a bug in your contract which you should fix.

There are two other ways to trigger exceptions: The `revert` function
can be used to flag an error and revert the current call. It is possible
to provide a string message containing details about the error that will
be passed back to the caller. The deprecated keyword `throw` can also be
used as an alternative to `revert()` (but only without error message).

::: tip

From version 0.4.13 the `throw` keyword is deprecated and will be phased
out in the future.
:::

When exceptions happen in a sub-call, they "bubble up" (i.e. exceptions
are rethrown) automatically. Exceptions to this rule are `send` and the
low-level functions `call`, `delegatecall` and `callcode` -- those
return `false` in case of an exception instead of "bubbling up".

::: warning

The low-level `call`, `delegatecall` and `callcode` will return success
if the called account is non-existent, as part of the design of EVM.
Existence must be checked prior to calling if desired.
:::

Catching exceptions is not yet possible.

In the following example, you can see how `require` can be used to
easily check conditions on inputs and how `assert` can be used for
internal error checking. Note that you can optionally provide a message
string for `require`, but not for `assert`.

    pragma solidity ^0.4.22;

    contract Sharer {
        function sendHalf(address addr) public payable returns (uint balance) {
            require(msg.value % 2 == 0, "Even value required.");
            uint balanceBeforeTransfer = this.balance;
            addr.transfer(msg.value / 2);
            // Since transfer throws an exception on failure and
            // cannot call back here, there should be no way for us to
            // still have half of the money.
            assert(this.balance == balanceBeforeTransfer - msg.value / 2);
            return this.balance;
        }
    }

An `assert`-style exception is generated in the following situations:

1.  If you access an array at a too large or negative index (i.e. `x[i]`
    where `i >= x.length` or `i < 0`).
2.  If you access a fixed-length `bytesN` at a too large or negative
    index.
3.  If you divide or modulo by zero (e.g. `5 / 0` or `23 % 0`).
4.  If you shift by a negative amount.
5.  If you convert a value too big or negative into an enum type.
6.  If you call a zero-initialized variable of internal function type.
7.  If you call `assert` with an argument that evaluates to false.

A `require`-style exception is generated in the following situations:

1.  Calling `throw`.
2.  Calling `require` with an argument that evaluates to `false`.
3.  If you call a function via a message call but it does not finish
    properly (i.e. it runs out of gas, has no matching function, or
    throws an exception itself), except when a low level operation
    `call`, `send`, `delegatecall` or `callcode` is used. The low level
    operations never throw exceptions but indicate failures by returning
    `false`.
4.  If you create a contract using the `new` keyword but the contract
    creation does not finish properly (see above for the definition of
    "not finish properly").
5.  If you perform an external function call targeting a contract that
    contains no code.
6.  If your contract receives Ether via a public function without
    `payable` modifier (including the constructor and the fallback
    function).
7.  If your contract receives Ether via a public getter function.
8.  If a `.transfer()` fails.

Internally, Solidity performs a revert operation (instruction `0xfd`)
for a `require`-style exception and executes an invalid operation
(instruction `0xfe`) to throw an `assert`-style exception. In both
cases, this causes the EVM to revert all changes made to the state. The
reason for reverting is that there is no safe way to continue execution,
because an expected effect did not occur. Because we want to retain the
atomicity of transactions, the safest thing to do is to revert all
changes and make the whole transaction (or at least call) without
effect. Note that `assert`-style exceptions consume all gas available to
the call, while `require`-style exceptions will not consume any gas
starting from the Metropolis release.

The following example shows how an error string can be used together
with revert and require:

    pragma solidity ^0.4.22;

    contract VendingMachine {
        function buy(uint amount) payable {
            if (amount > msg.value / 2 ether)
                revert("Not enough Ether provided.");
            // Alternative way to do it:
            require(
                amount <= msg.value / 2 ether,
                "Not enough Ether provided."
            );
            // Perform the purchase.
        }
    }

The provided string will be [abi-encoded ](./abi-spec.md#abi-encoded-) as if it were a call to a function `Error(string)`. In the
above example, `revert("Not enough Ether provided.");` will cause the
following hexadecimal data be set as error return data:

``` {.}
0x08c379a0                                                         // Function selector for Error(string)
0x0000000000000000000000000000000000000000000000000000000000000020 // Data offset
0x000000000000000000000000000000000000000000000000000000000000001a // String length
0x4e6f7420656e6f7567682045746865722070726f76696465642e000000000000 // String data
```
