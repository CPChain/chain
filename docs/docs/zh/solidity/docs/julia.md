# Joyfully Universal Language for (Inline) Assembly

::: 
JULIA is an intermediate language that can compile to various different
backends (EVM 1.0, EVM 1.5 and eWASM are planned). Because of that, it
is designed to be a usable common denominator of all three platforms. It
can already be used for "inline assembly" inside Solidity and future
versions of the Solidity compiler will even use JULIA as intermediate
language. It should also be easy to build high-level optimizer stages
for JULIA.
:::

::: tip

Note that the flavour used for "inline assembly" does not have types
(everything is `u256`) and the built-in functions are identical to the
EVM opcodes. Please resort to the inline assembly documentation for
details.
:::

The core components of JULIA are functions, blocks, variables, literals,
for-loops, if-statements, switch-statements, expressions and assignments
to variables.

JULIA is typed, both variables and literals must specify the type with
postfix notation. The supported types are `bool`, `u8`, `s8`, `u32`,
`s32`, `u64`, `s64`, `u128`, `s128`, `u256` and `s256`.

JULIA in itself does not even provide operators. If the EVM is targeted,
opcodes will be available as built-in functions, but they can be
reimplemented if the backend changes. For a list of mandatory built-in
functions, see the section below.

The following example program assumes that the EVM opcodes `mul`, `div`
and `mod` are available either natively or as functions and computes
exponentiation.

``` {.}
{
    function power(base:u256, exponent:u256) -> result:u256
    {
        switch exponent
        case 0:u256 { result := 1:u256 }
        case 1:u256 { result := base }
        default:
        {
            result := power(mul(base, base), div(exponent, 2:u256))
            switch mod(exponent, 2:u256)
                case 1:u256 { result := mul(base, result) }
        }
    }
}
```

It is also possible to implement the same function using a for-loop
instead of with recursion. Here, we need the EVM opcodes `lt`
(less-than) and `add` to be available.

``` {.}
{
    function power(base:u256, exponent:u256) -> result:u256
    {
        result := 1:u256
        for { let i := 0:u256 } lt(i, exponent) { i := add(i, 1:u256) }
        {
            result := mul(result, base)
        }
    }
}
```

## Specification of JULIA

JULIA code is described in this chapter. JULIA code is usually placed
into a JULIA object, which is described in the following chapter.

Grammar:

    Block = '{' Statement* '}'
    Statement =
        Block |
        FunctionDefinition |
        VariableDeclaration |
        Assignment |
        Expression |
        Switch |
        ForLoop |
        BreakContinue
    FunctionDefinition =
        'function' Identifier '(' TypedIdentifierList? ')'
        ( '->' TypedIdentifierList )? Block
    VariableDeclaration =
        'let' TypedIdentifierList ( ':=' Expression )?
    Assignment =
        IdentifierList ':=' Expression
    Expression =
        FunctionCall | Identifier | Literal
    If =
        'if' Expression Block
    Switch =
        'switch' Expression Case* ( 'default' Block )?
    Case =
        'case' Literal Block
    ForLoop =
        'for' Block Expression Block Block
    BreakContinue =
        'break' | 'continue'
    FunctionCall =
        Identifier '(' ( Expression ( ',' Expression )* )? ')'
    Identifier = [a-zA-Z_$] [a-zA-Z_0-9]*
    IdentifierList = Identifier ( ',' Identifier)*
    TypeName = Identifier | BuiltinTypeName
    BuiltinTypeName = 'bool' | [us] ( '8' | '32' | '64' | '128' | '256' )
    TypedIdentifierList = Identifier ':' TypeName ( ',' Identifier ':' TypeName )*
    Literal =
        (NumberLiteral | StringLiteral | HexLiteral | TrueLiteral | FalseLiteral) ':' TypeName
    NumberLiteral = HexNumber | DecimalNumber
    HexLiteral = 'hex' ('"' ([0-9a-fA-F]{2})* '"' | '\'' ([0-9a-fA-F]{2})* '\'')
    StringLiteral = '"' ([^"\r\n\\] | '\\' .)* '"'
    TrueLiteral = 'true'
    FalseLiteral = 'false'
    HexNumber = '0x' [0-9a-fA-F]+
    DecimalNumber = [0-9]+

### Restrictions on the Grammar

Switches must have at least one case (including the default case). If
all possible values of the expression is covered, the default case
should not be allowed (i.e. a switch with a `bool` expression and having
both a true and false case should not allow a default case).

Every expression evaluates to zero or more values. Identifiers and
Literals evaluate to exactly one value and function calls evaluate to a
number of values equal to the number of return values of the function
called.

In variable declarations and assignments, the right-hand-side expression
(if present) has to evaluate to a number of values equal to the number
of variables on the left-hand-side. This is the only situation where an
expression evaluating to more than one value is allowed.

Expressions that are also statements (i.e. at the block level) have to
evaluate to zero values.

In all other situations, expressions have to evaluate to exactly one
value.

The `continue` and `break` statements can only be used inside loop
bodies and have to be in the same function as the loop (or both have to
be at the top level). The condition part of the for-loop has to evaluate
to exactly one value.

Literals cannot be larger than the their type. The largest type defined
is 256-bit wide.

### Scoping Rules

Scopes in JULIA are tied to Blocks (exceptions are functions and the for
loop as explained below) and all declarations (`FunctionDefinition`,
`VariableDeclaration`) introduce new identifiers into these scopes.

Identifiers are visible in the block they are defined in (including all
sub-nodes and sub-blocks). As an exception, identifiers defined in the
"init" part of the for-loop (the first block) are visible in all other
parts of the for-loop (but not outside of the loop). Identifiers
declared in the other parts of the for loop respect the regular
syntatical scoping rules. The parameters and return parameters of
functions are visible in the function body and their names cannot
overlap.

Variables can only be referenced after their declaration. In particular,
variables cannot be referenced in the right hand side of their own
variable declaration. Functions can be referenced already before their
declaration (if they are visible).

Shadowing is disallowed, i.e. you cannot declare an identifier at a
point where another identifier with the same name is also visible, even
if it is not accessible.

Inside functions, it is not possible to access a variable that was
declared outside of that function.

### Formal Specification

We formally specify JULIA by providing an evaluation function E
overloaded on the various nodes of the AST. Any functions can have side
effects, so E takes two state objects and the AST node and returns two
new state objects and a variable number of other values. The two state
objects are the global state object (which in the context of the EVM is
the memory, storage and state of the blockchain) and the local state
object (the state of local variables, i.e. a segment of the stack in the
EVM). If the AST node is a statement, E returns the two state objects
and a "mode", which is used for the `break` and `continue` statements.
If the AST node is an expression, E returns the two state objects and as
many values as the expression evaluates to.

The exact nature of the global state is unspecified for this high level
description. The local state `L` is a mapping of identifiers `i` to
values `v`, denoted as `L[i] = v`.

For an identifier `v`, let `$v` be the name of the identifier.

We will use a destructuring notation for the AST nodes.

``` {.}
E(G, L, <{St1, ..., Stn}>: Block) =
    let G1, L1, mode = E(G, L, St1, ..., Stn)
    let L2 be a restriction of L1 to the identifiers of L
    G1, L2, mode
E(G, L, St1, ..., Stn: Statement) =
    if n is zero:
        G, L, regular
    else:
        let G1, L1, mode = E(G, L, St1)
        if mode is regular then
            E(G1, L1, St2, ..., Stn)
        otherwise
            G1, L1, mode
E(G, L, FunctionDefinition) =
    G, L, regular
E(G, L, <let var1, ..., varn := rhs>: VariableDeclaration) =
    E(G, L, <var1, ..., varn := rhs>: Assignment)
E(G, L, <let var1, ..., varn>: VariableDeclaration) =
    let L1 be a copy of L where L1[$vari] = 0 for i = 1, ..., n
    G, L1, regular
E(G, L, <var1, ..., varn := rhs>: Assignment) =
    let G1, L1, v1, ..., vn = E(G, L, rhs)
    let L2 be a copy of L1 where L2[$vari] = vi for i = 1, ..., n
    G, L2, regular
E(G, L, <for { i1, ..., in } condition post body>: ForLoop) =
    if n >= 1:
        let G1, L1, mode = E(G, L, i1, ..., in)
        // mode has to be regular due to the syntactic restrictions
        let G2, L2, mode = E(G1, L1, for {} condition post body)
        // mode has to be regular due to the syntactic restrictions
        let L3 be the restriction of L2 to only variables of L
        G2, L3, regular
    else:
        let G1, L1, v = E(G, L, condition)
        if v is false:
            G1, L1, regular
        else:
            let G2, L2, mode = E(G1, L, body)
            if mode is break:
                G2, L2, regular
            else:
                G3, L3, mode = E(G2, L2, post)
                E(G3, L3, for {} condition post body)
E(G, L, break: BreakContinue) =
    G, L, break
E(G, L, continue: BreakContinue) =
    G, L, continue
E(G, L, <if condition body>: If) =
    let G0, L0, v = E(G, L, condition)
    if v is true:
        E(G0, L0, body)
    else:
        G0, L0, regular
E(G, L, <switch condition case l1:t1 st1 ... case ln:tn stn>: Switch) =
    E(G, L, switch condition case l1:t1 st1 ... case ln:tn stn default {})
E(G, L, <switch condition case l1:t1 st1 ... case ln:tn stn default st'>: Switch) =
    let G0, L0, v = E(G, L, condition)
    // i = 1 .. n
    // Evaluate literals, context doesn't matter
    let _, _, v1 = E(G0, L0, l1)
    ...
    let _, _, vn = E(G0, L0, ln)
    if there exists smallest i such that vi = v:
        E(G0, L0, sti)
    else:
        E(G0, L0, st')

E(G, L, <name>: Identifier) =
    G, L, L[$name]
E(G, L, <fname(arg1, ..., argn)>: FunctionCall) =
    G1, L1, vn = E(G, L, argn)
    ...
    G(n-1), L(n-1), v2 = E(G(n-2), L(n-2), arg2)
    Gn, Ln, v1 = E(G(n-1), L(n-1), arg1)
    Let <function fname (param1, ..., paramn) -> ret1, ..., retm block>
    be the function of name $fname visible at the point of the call.
    Let L' be a new local state such that
    L'[$parami] = vi and L'[$reti] = 0 for all i.
    Let G'', L'', mode = E(Gn, L', block)
    G'', Ln, L''[$ret1], ..., L''[$retm]
E(G, L, l: HexLiteral) = G, L, hexString(l),
    where hexString decodes l from hex and left-aligns it into 32 bytes
E(G, L, l: StringLiteral) = G, L, utf8EncodeLeftAligned(l),
    where utf8EncodeLeftAligned performs a utf8 encoding of l
    and aligns it left into 32 bytes
E(G, L, n: HexNumber) = G, L, hex(n)
    where hex is the hexadecimal decoding function
E(G, L, n: DecimalNumber) = G, L, dec(n),
    where dec is the decimal decoding function
```

### Type Conversion Functions

JULIA has no support for implicit type conversion and therefore
functions exists to provide explicit conversion. When converting a
larger type to a shorter type a runtime exception can occur in case of
an overflow.

Truncating conversions are supported between the following types:

:   -   `bool`
    -   `u32`
    -   `u64`
    -   `u256`
    -   `s256`

For each of these a type conversion function exists having the prototype
in the form of
`<input_type>to<output_type>(x:<input_type>) -> y:<output_type>`, such
as `u32tobool(x:u32) -> y:bool`, `u256tou32(x:u256) -> y:u32` or
`s256tou256(x:s256) -> y:u256`.

::: tip

`u32tobool(x:u32) -> y:bool` can be implemented as
`y := not(iszerou256(x))` and `booltou32(x:bool) -> y:u32` can be
implemented as
`switch x case true:bool { y := 1:u32 } case false:bool { y := 0:u32 }`
:::

### Low-level Functions

The following functions must be available:

<table cellspacing="0" cellpadding="5">
	
	<tr>
		<td  rowspan="1"> *Logic* </td>
	</tr>
	<tr>
		<td  rowspan="1"> not(x:bool) -> z:bool </td>
		<td  rowspan="1"> logical not </td>
	</tr>
	<tr>
		<td  rowspan="1"> and(x:bool, y:bool) -> z:bool </td>
		<td  rowspan="1"> logical and </td>
	</tr>
	<tr>
		<td  rowspan="1"> or(x:bool, y:bool) -> z:bool </td>
		<td  rowspan="1"> logical or </td>
	</tr>
	<tr>
		<td  rowspan="1"> xor(x:bool, y:bool) -> z:bool </td>
		<td  rowspan="1"> xor </td>
	</tr>
	<tr>
		<td  rowspan="1"> *Arithmetics* </td>
	</tr>
	<tr>
		<td  rowspan="1"> addu256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> x + y </td>
	</tr>
	<tr>
		<td  rowspan="1"> subu256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> x - y </td>
	</tr>
	<tr>
		<td  rowspan="1"> mulu256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> x * y </td>
	</tr>
	<tr>
		<td  rowspan="1"> divu256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> x / y </td>
	</tr>
	<tr>
		<td  rowspan="1"> divs256(x:s256, y:s256) -> z:s256 </td>
		<td  rowspan="1"> x / y, for signed numbers in two's complement </td>
	</tr>
	<tr>
		<td  rowspan="1"> modu256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> x % y </td>
	</tr>
	<tr>
		<td  rowspan="1"> mods256(x:s256, y:s256) -> z:s256 </td>
		<td  rowspan="1"> x % y, for signed numbers in two's complement </td>
	</tr>
	<tr>
		<td  rowspan="1"> signextendu256(i:u256, x:u256) -> z:u256 </td>
		<td  rowspan="1"> sign extend from (i*8+7)th bit counting from least significant </td>
	</tr>
	<tr>
		<td  rowspan="1"> expu256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> x to the power of y </td>
	</tr>
	<tr>
		<td  rowspan="1"> addmodu256(x:u256, y:u256, m:u256) -> z:u256</td>
		<td  rowspan="1"> (x + y) % m with arbitrary precision arithmetics </td>
	</tr>
	<tr>
		<td  rowspan="1"> mulmodu256(x:u256, y:u256, m:u256) -> z:u256</td>
		<td  rowspan="1"> (x * y) % m with arbitrary precision arithmetics </td>
	</tr>
	<tr>
		<td  rowspan="1"> ltu256(x:u256, y:u256) -> z:bool </td>
		<td  rowspan="1"> true if x < y, false otherwise </td>
	</tr>
	<tr>
		<td  rowspan="1"> gtu256(x:u256, y:u256) -> z:bool </td>
		<td  rowspan="1"> true if x > y, false otherwise </td>
	</tr>
	<tr>
		<td  rowspan="1"> sltu256(x:s256, y:s256) -> z:bool </td>
		<td  rowspan="1"> true if x < y, false otherwise (for signed numbers in two's complement) </td>
	</tr>
	<tr>
		<td  rowspan="1"> sgtu256(x:s256, y:s256) -> z:bool </td>
		<td  rowspan="1"> true if x > y, false otherwise (for signed numbers in two's complement) </td>
	</tr>
	<tr>
		<td  rowspan="1"> equ256(x:u256, y:u256) -> z:bool </td>
		<td  rowspan="1"> true if x == y, false otherwise </td>
	</tr>
	<tr>
		<td  rowspan="1"> iszerou256(x:u256) -> z:bool </td>
		<td  rowspan="1"> true if x == 0, false otherwise </td>
	</tr>
	<tr>
		<td  rowspan="1"> notu256(x:u256) -> z:u256 </td>
		<td  rowspan="1"> ~x, every bit of x is negated </td>
	</tr>
	<tr>
		<td  rowspan="1"> andu256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> bitwise and of x and y </td>
	</tr>
	<tr>
		<td  rowspan="1"> oru256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> bitwise or of x and y </td>
	</tr>
	<tr>
		<td  rowspan="1"> xoru256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> bitwise xor of x and y </td>
	</tr>
	<tr>
		<td  rowspan="1"> shlu256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> logical left shift of x by y </td>
	</tr>
	<tr>
		<td  rowspan="1"> shru256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> logical right shift of x by y </td>
	</tr>
	<tr>
		<td  rowspan="1"> saru256(x:u256, y:u256) -> z:u256 </td>
		<td  rowspan="1"> arithmetic right shift of x by y </td>
	</tr>
	<tr>
		<td  rowspan="1"> byte(n:u256, x:u256) -> v:u256 </td>
		<td  rowspan="1"> nth byte of x, where the most significant byte is the 0th byte Cannot this be just replaced by and256(shr256(n, x), 0xff) and let it be optimised out by the EVM backend? </td>
	</tr>
	<tr>
		<td  rowspan="1"> *Memory and storage* </td>
	</tr>
	<tr>
		<td  rowspan="1"> mload(p:u256) -> v:u256 </td>
		<td  rowspan="1"> mem[p..(p+32)) </td>
	</tr>
	<tr>
		<td  rowspan="1"> mstore(p:u256, v:u256) </td>
		<td  rowspan="1"> mem[p..(p+32)) := v </td>
	</tr>
	<tr>
		<td  rowspan="1"> mstore8(p:u256, v:u256) </td>
		<td  rowspan="1"> mem[p] := v & 0xff - only modifies a single byte </td>
	</tr>
	<tr>
		<td  rowspan="1"> sload(p:u256) -> v:u256 </td>
		<td  rowspan="1"> storage[p] </td>
	</tr>
	<tr>
		<td  rowspan="1"> sstore(p:u256, v:u256) </td>
		<td  rowspan="1"> storage[p] := v </td>
	</tr>
	<tr>
		<td  rowspan="1"> msize() -> size:u256 </td>
		<td  rowspan="1"> size of memory, i.e. largest accessed memory index, albeit due due to the memory extension function, which extends by words, this will always be a multiple of 32 bytes </td>
	</tr>
	<tr>
		<td  rowspan="1"> *Execution control* </td>
	</tr>
	<tr>
		<td  rowspan="1"> create(v:u256, p:u256, s:u256) </td>
		<td  rowspan="1"> create new contract with code mem[p..(p+s)) and send v wei and return the new address </td>
	</tr>
	<tr>
		<td  rowspan="1"> call(g:u256, a:u256, v:u256, in:u256, insize:u256, out:u256, outsize:u256) -> r:u256 </td>
		<td  rowspan="1"> call contract at address a with input mem[in..(in+insize)) providing g gas and v wei and output area mem[out..(out+outsize)) returning 0 on error (eg. out of gas) and 1 on success </td>
	</tr>
	<tr>
		<td  rowspan="1"> callcode(g:u256, a:u256, v:u256, in:u256, insize:u256, out:u256, outsize:u256) -> r:u256 </td>
		<td  rowspan="1"> identical to <code>call</code> but only use the code from a and stay in the context of the current contract otherwise </td>
	</tr>
	<tr>
		<td  rowspan="1"> delegatecall(g:u256, a:u256, in:u256, insize:u256, out:u256, outsize:u256) -> r:u256 </td>
		<td  rowspan="1"> identical to <code>callcode</code>, but also keep <code>caller</code> and <code>callvalue</code> </td>
	</tr>
	<tr>
		<td  rowspan="1"> abort() </td>
		<td  rowspan="1"> abort (equals to invalid instruction on EVM) </td>
	</tr>
	<tr>
		<td  rowspan="1"> return(p:u256, s:u256) </td>
		<td  rowspan="1"> end execution, return data mem[p..(p+s)) </td>
	</tr>
	<tr>
		<td  rowspan="1"> revert(p:u256, s:u256) </td>
		<td  rowspan="1"> end execution, revert state changes, return data mem[p..(p+s)) </td>
	</tr>
	<tr>
		<td  rowspan="1"> selfdestruct(a:u256) </td>
		<td  rowspan="1"> end execution, destroy current contract and send funds to a </td>
	</tr>
	<tr>
		<td  rowspan="1"> log0(p:u256, s:u256) </td>
		<td  rowspan="1"> log without topics and data mem[p..(p+s)) </td>
	</tr>
	<tr>
		<td  rowspan="1"> log1(p:u256, s:u256, t1:u256) </td>
		<td  rowspan="1"> log with topic t1 and data mem[p..(p+s)) </td>
	</tr>
	<tr>
		<td  rowspan="1"> log2(p:u256, s:u256, t1:u256, t2:u256) </td>
		<td  rowspan="1"> log with topics t1, t2 and data mem[p..(p+s)) </td>
	</tr>
	<tr>
		<td  rowspan="1"> log3(p:u256, s:u256, t1:u256, t2:u256, t3:u256) </td>
		<td  rowspan="1"> log with topics t, t2, t3 and data mem[p..(p+s)) </td>
	</tr>
	<tr>
		<td  rowspan="1"> log4(p:u256, s:u256, t1:u256, t2:u256, t3:u256, t4:u256) </td>
		<td  rowspan="1"> log with topics t1, t2, t3, t4 and data mem[p..(p+s)) </td>
	</tr>
	<tr>
		<td  rowspan="1"> *State queries* </td>
	</tr>
	<tr>
		<td  rowspan="1"> blockcoinbase() -> address:u256 </td>
		<td  rowspan="1"> current mining beneficiary </td>
	</tr>
	<tr>
		<td  rowspan="1"> blockdifficulty() -> difficulty:u256 </td>
		<td  rowspan="1"> difficulty of the current block </td>
	</tr>
	<tr>
		<td  rowspan="1"> blockgaslimit() -> limit:u256 </td>
		<td  rowspan="1"> block gas limit of the current block </td>
	</tr>
	<tr>
		<td  rowspan="1"> blockhash(b:u256) -> hash:u256 </td>
		<td  rowspan="1"> hash of block nr b - only for last 256 blocks excluding current </td>
	</tr>
	<tr>
		<td  rowspan="1"> blocknumber() -> block:u256 </td>
		<td  rowspan="1"> current block number </td>
	</tr>
	<tr>
		<td  rowspan="1"> blocktimestamp() -> timestamp:u256 </td>
		<td  rowspan="1"> timestamp of the current block in seconds since the epoch </td>
	</tr>
	<tr>
		<td  rowspan="1"> txorigin() -> address:u256 </td>
		<td  rowspan="1"> transaction sender </td>
	</tr>
	<tr>
		<td  rowspan="1"> txgasprice() -> price:u256 </td>
		<td  rowspan="1"> gas price of the transaction </td>
	</tr>
	<tr>
		<td  rowspan="1"> gasleft() -> gas:u256 </td>
		<td  rowspan="1"> gas still available to execution </td>
	</tr>
	<tr>
		<td  rowspan="1"> balance(a:u256) -> v:u256 </td>
		<td  rowspan="1"> wei balance at address a </td>
	</tr>
	<tr>
		<td  rowspan="1"> this() -> address:u256 </td>
		<td  rowspan="1"> address of the current contract / execution context </td>
	</tr>
	<tr>
		<td  rowspan="1"> caller() -> address:u256 </td>
		<td  rowspan="1"> call sender (excluding delegatecall) </td>
	</tr>
	<tr>
		<td  rowspan="1"> callvalue() -> v:u256 </td>
		<td  rowspan="1"> wei sent together with the current call </td>
	</tr>
	<tr>
		<td  rowspan="1"> calldataload(p:u256) -> v:u256 </td>
		<td  rowspan="1"> call data starting from position p (32 bytes) </td>
	</tr>
	<tr>
		<td  rowspan="1"> calldatasize() -> v:u256 </td>
		<td  rowspan="1"> size of call data in bytes </td>
	</tr>
	<tr>
		<td  rowspan="1"> calldatacopy(t:u256, f:u256, s:u256) </td>
		<td  rowspan="1"> copy s bytes from calldata at position f to mem at position t </td>
	</tr>
	<tr>
		<td  rowspan="1"> codesize() -> size:u256 </td>
		<td  rowspan="1"> size of the code of the current contract / execution context </td>
	</tr>
	<tr>
		<td  rowspan="1"> codecopy(t:u256, f:u256, s:u256) </td>
		<td  rowspan="1"> copy s bytes from code at position f to mem at position t </td>
	</tr>
	<tr>
		<td  rowspan="1"> extcodesize(a:u256) -> size:u256 </td>
		<td  rowspan="1"> size of the code at address a </td>
	</tr>
	<tr>
		<td  rowspan="1"> extcodecopy(a:u256, t:u256, f:u256, s:u256) </td>
		<td  rowspan="1"> like codecopy(t, f, s) but take code at address a </td>
	</tr>
	<tr>
		<td  rowspan="1"> *Others* </td>
	</tr>
	<tr>
		<td  rowspan="1"> discard(unused:bool) </td>
		<td  rowspan="1"> discard value </td>
	</tr>
	<tr>
		<td  rowspan="1"> discardu256(unused:u256) </td>
		<td  rowspan="1"> discard value </td>
	</tr>
	<tr>
		<td  rowspan="1"> splitu256tou64(x:u256) -> (x1:u64, x2:u64, x3:u64, x4:u64) </td>
		<td  rowspan="1"> split u256 to four u64's </td>
	</tr>
	<tr>
		<td  rowspan="1"> combineu64tou256(x1:u64, x2:u64, x3:u64, x4:u64) -> (x:u256) </td>
		<td  rowspan="1"> combine four u64's into a single u256 </td>
	</tr>
	<tr>
		<td  rowspan="1"> keccak256(p:u256, s:u256) -> v:u256 </td>
		<td  rowspan="1"> keccak(mem[p...(p+s))) </td>
	</tr>
</table>

### Backends

Backends or targets are the translators from JULIA to a specific
bytecode. Each of the backends can expose functions prefixed with the
name of the backend. We reserve `evm_` and `ewasm_` prefixes for the two
proposed backends.

### Backend: EVM

The EVM target will have all the underlying EVM opcodes exposed with the
[evm\_]{.title-ref} prefix.

### Backend: "EVM 1.5" 

TBD

### Backend: eWASM

TBD

## Specification of JULIA Object

Grammar:

    TopLevelObject = 'object' '{' Code? ( Object | Data )* '}'
    Object = 'object' StringLiteral '{' Code? ( Object | Data )* '}'
    Code = 'code' Block
    Data = 'data' StringLiteral HexLiteral
    HexLiteral = 'hex' ('"' ([0-9a-fA-F]{2})* '"' | '\'' ([0-9a-fA-F]{2})* '\'')
    StringLiteral = '"' ([^"\r\n\\] | '\\' .)* '"'

Above, `Block` refers to `Block` in the JULIA code grammar explained in
the previous chapter.

An example JULIA Object is shown below:

..code:

    // Code consists of a single object. A single "code" node is the code of the object.
    // Every (other) named object or data section is serialized and
    // made accessible to the special built-in functions datacopy / dataoffset / datasize
    object {
        code {
            let size = datasize("runtime")
            let offset = allocate(size)
            // This will turn into a memory->memory copy for eWASM and
            // a codecopy for EVM
            datacopy(dataoffset("runtime"), offset, size)
            // this is a constructor and the runtime code is returned
            return(offset, size)
        }

        data "Table2" hex"4123"

        object "runtime" {
            code {
                // runtime code

                let size = datasize("Contract2")
                let offset = allocate(size)
                // This will turn into a memory->memory copy for eWASM and
                // a codecopy for EVM
                datacopy(dataoffset("Contract2"), offset, size)
                // constructor parameter is a single number 0x1234
                mstore(add(offset, size), 0x1234)
                create(offset, add(size, 32))
            }

            // Embedded object. Use case is that the outside is a factory contract,
            // and Contract2 is the code to be created by the factory
            object "Contract2" {
                code {
                    // code here ...
                }

                object "runtime" {
                    code {
                        // code here ...
                    }
                 }

                 data "Table1" hex"4123"
            }
        }
    }
