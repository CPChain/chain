# Layout of a Solidity Source File

Source files can contain an arbitrary number of contract definitions,
include directives and pragma directives.

## Version Pragma 

Source files can (and should) be annotated with a so-called version
pragma to reject being compiled with future compiler versions that might
introduce incompatible changes. We try to keep such changes to an
absolute minimum and especially introduce changes in a way that changes
in semantics will also require changes in the syntax, but this is of
course not always possible. Because of that, it is always a good idea to
read through the changelog at least for releases that contain breaking
changes, those releases will always have versions of the form `0.x.0` or
`x.0.0`.

The version pragma is used as follows:

    pragma solidity ^0.4.0;

Such a source file will not compile with a compiler earlier than version
0.4.0 and it will also not work on a compiler starting from version
0.5.0 (this second condition is added by using `^`). The idea behind
this is that there will be no breaking changes until version `0.5.0`, so
we can always be sure that our code will compile the way we intended it
to. We do not fix the exact version of the compiler, so that bugfix
releases are still possible.

It is possible to specify much more complex rules for the compiler
version, the expression follows those used by
[npm](https://docs.npmjs.com/misc/semver).

## Importing other Source Files 

### Syntax and Semantics

Solidity supports import statements that are very similar to those
available in JavaScript (from ES6 on), although Solidity does not know
the concept of a "default export".

At a global level, you can use import statements of the following form:

    import "filename";

This statement imports all global symbols from "filename" (and symbols
imported there) into the current global scope (different than in ES6 but
backwards-compatible for Solidity).

    import * as symbolName from "filename";

...creates a new global symbol `symbolName` whose members are all the
global symbols from `"filename"`.

    import {symbol1 as alias, symbol2} from "filename";

...creates new global symbols `alias` and `symbol2` which reference
`symbol1` and `symbol2` from `"filename"`, respectively.

Another syntax is not part of ES6, but probably convenient:

    import "filename" as symbolName;

which is equivalent to `import * as symbolName from "filename";`.

### Paths

In the above, `filename` is always treated as a path with `/` as
directory separator, `.` as the current and `..` as the parent
directory. When `.` or `..` is followed by a character except `/`, it is
not considered as the current or the parent directory. All path names
are treated as absolute paths unless they start with the current `.` or
the parent directory `..`.

To import a file `x` from the same directory as the current file, use
`import "./x" as x;`. If you use `import "x" as x;` instead, a different
file could be referenced (in a global "include directory").

It depends on the compiler (see below) how to actually resolve the
paths. In general, the directory hierarchy does not need to strictly map
onto your local filesystem, it can also map to resources discovered via
e.g. ipfs, http or git.

### Use in Actual Compilers

When the compiler is invoked, it is not only possible to specify how to
discover the first element of a path, but it is possible to specify path
prefix remappings so that e.g. `github.com/ethereum/dapp-bin/library` is
remapped to `/usr/local/dapp-bin/library` and the compiler will read the
files from there. If multiple remappings can be applied, the one with
the longest key is tried first. This allows for a "fallback-remapping"
with e.g. `""` maps to `"/usr/local/include/solidity"`. Furthermore,
these remappings can depend on the context, which allows you to
configure packages to import e.g. different versions of a library of the
same name.

**solc**:

For solc (the commandline compiler), these remappings are provided as
`context:prefix=target` arguments, where both the `context:` and the
`=target` parts are optional (where target defaults to prefix in that
case). All remapping values that are regular files are compiled
(including their dependencies). This mechanism is completely
backwards-compatible (as long as no filename contains = or :) and thus
not a breaking change. All imports in files in or below the directory
`context` that import a file that starts with `prefix` are redirected by
replacing `prefix` by `target`.

So as an example, if you clone `github.com/ethereum/dapp-bin/` locally
to `/usr/local/dapp-bin`, you can use the following in your source file:

    import "github.com/ethereum/dapp-bin/library/iterable_mapping.sol" as it_mapping;

and then run the compiler as

``` {.bash}
solc github.com/ethereum/dapp-bin/=/usr/local/dapp-bin/ source.sol
```

As a more complex example, suppose you rely on some module that uses a
very old version of dapp-bin. That old version of dapp-bin is checked
out at `/usr/local/dapp-bin_old`, then you can use

``` {.bash}
solc module1:github.com/ethereum/dapp-bin/=/usr/local/dapp-bin/ \
     module2:github.com/ethereum/dapp-bin/=/usr/local/dapp-bin_old/ \
     source.sol
```

so that all imports in `module2` point to the old version but imports in
`module1` get the new version.

Note that solc only allows you to include files from certain
directories: They have to be in the directory (or subdirectory) of one
of the explicitly specified source files or in the directory (or
subdirectory) of a remapping target. If you want to allow direct
absolute includes, just add the remapping `=/`.

If there are multiple remappings that lead to a valid file, the
remapping with the longest common prefix is chosen.

**Remix**:

[Remix](https://remix.ethereum.org/) provides an automatic remapping for
github and will also automatically retrieve the file over the network:
You can import the iterable mapping by e.g.
`import "github.com/ethereum/dapp-bin/library/iterable_mapping.sol" as it_mapping;`.

Other source code providers may be added in the future.

## Comments

Single-line comments (`//`) and multi-line comments (`/*...*/`) are
possible.

    // This is a single-line comment.

    /*
    This is a
    multi-line comment.
    */

Additionally, there is another type of comment called a natspec comment,
for which the documentation is not yet written. They are written with a
triple slash (`///`) or a double asterisk block(`/** ... */`) and they
should be used directly above function declarations or statements. You
can use [Doxygen](https://en.wikipedia.org/wiki/Doxygen)-style tags
inside these comments to document functions, annotate conditions for
formal verification, and provide a **confirmation text** which is shown
to users when they attempt to invoke a function.

In the following example we document the title of the contract, the
explanation for the two input parameters and two returned values.

    pragma solidity ^0.4.0;

    /** @title Shape calculator. */
    contract shapeCalculator {
        /** @dev Calculates a rectangle's surface and perimeter.
          * @param w Width of the rectangle.
          * @param h Height of the rectangle.
          * @return s The calculated surface.
          * @return p The calculated perimeter.
          */
        function rectangle(uint w, uint h) returns (uint s, uint p) {
            s = w * h;
            p = 2 * (w + h);
        }
    }
