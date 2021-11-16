# Solidity

Back to [CPChain Docs](../index.html).

<div align=center>
    <img src="./logo.svg" width="120px"/>
</div>

Solidity is a contract-oriented, high-level language for implementing
smart contracts. It was influenced by C++, Python and JavaScript and is
designed to target the Ethereum Virtual Machine (EVM).

Solidity is statically typed, supports inheritance, libraries and
complex user-defined types among other features.

As you will see, it is possible to create contracts for voting,
crowdfunding, blind auctions, multi-signature wallets and more.

::: warning

The solidity version for CPChain is 0.4.25. Other version is not
guaranteed compatible with CPChain.
:::

::: tip

The best way to try out Solidity right now is using
[Remix](https://remix.ethereum.org/) (it can take a while to load,
please be patient). Remix is a web browser based IDE that allows you to
write Solidity smart contracts, then deploy and run the smart contracts.
:::

::: warning

Since software is written by humans, it can have bugs. Thus, also smart
contracts should be created following well-known best-practices in
software development. This includes code review, testing, audits and
correctness proofs. Also note that users are sometimes more confident in
code than its authors. Finally, blockchains have their own things to
watch out for, so please take a look at the section
[Security Considerations](./security-considerations.md#security-considerations).
:::

## Translations

This documentation is translated into several languages by community
volunteers, but the English version stands as a reference.

-   [Simplified Chinese](http://solidity-cn.readthedocs.io) (in
    progress)
-   [Spanish](https://solidity-es.readthedocs.io)
-   [Russian](https://github.com/ethereum/wiki/wiki/%5BRussian%5D-%D0%A0%D1%83%D0%BA%D0%BE%D0%B2%D0%BE%D0%B4%D1%81%D1%82%D0%B2%D0%BE-%D0%BF%D0%BE-Solidity)
    (rather outdated)
-   [Korean](http://solidity-kr.readthedocs.io) (in progress)

## Useful links

-   [Ethereum](https://ethereum.org)
-   [Changelog](https://github.com/ethereum/solidity/blob/develop/Changelog.md)
-   [Story Backlog](https://www.pivotaltracker.com/n/projects/1189488)
-   [Source Code](https://github.com/ethereum/solidity/)
-   [Ethereum Stackexchange](https://ethereum.stackexchange.com/)
-   [Gitter Chat](https://gitter.im/ethereum/solidity/)

## Available Solidity Integrations

-   

    [Remix](https://remix.ethereum.org/)

    :   Browser-based IDE with integrated compiler and Solidity runtime
        environment without server-side components.

-   

    [IntelliJ IDEA plugin](https://plugins.jetbrains.com/plugin/9475-intellij-solidity)

    :   Solidity plugin for IntelliJ IDEA (and all other JetBrains IDEs)

-   

    [Visual Studio Extension](https://visualstudiogallery.msdn.microsoft.com/96221853-33c4-4531-bdd5-d2ea5acc4799/)

    :   Solidity plugin for Microsoft Visual Studio that includes the
        Solidity compiler.

-   

    [Package for SublimeText --- Solidity language syntax](https://packagecontrol.io/packages/Ethereum/)

    :   Solidity syntax highlighting for SublimeText editor.

-   

    [Etheratom](https://github.com/0mkara/etheratom)

    :   Plugin for the Atom editor that features syntax highlighting,
        compilation and a runtime environment (Backend node & VM
        compatible).

-   

    [Atom Solidity Linter](https://atom.io/packages/linter-solidity)

    :   Plugin for the Atom editor that provides Solidity linting.

-   

    [Atom Solium Linter](https://atom.io/packages/linter-solium)

    :   Configurable Solidty linter for Atom using Solium as a base.

-   

    [Solium](https://github.com/duaraghav8/Solium/)

    :   Linter to identify and fix style and security issues in
        Solidity.

-   

    [Solhint](https://github.com/protofire/solhint)

    :   Solidity linter that provides security, style guide and best
        practice rules for smart contract validation.

-   

    [Visual Studio Code extension](http://juan.blanco.ws/solidity-contracts-in-visual-studio-code/)

    :   Solidity plugin for Microsoft Visual Studio Code that includes
        syntax highlighting and the Solidity compiler.

-   

    [Emacs Solidity](https://github.com/ethereum/emacs-solidity/)

    :   Plugin for the Emacs editor providing syntax highlighting and
        compilation error reporting.

-   

    [Vim Solidity](https://github.com/tomlion/vim-solidity/)

    :   Plugin for the Vim editor providing syntax highlighting.

-   

    [Vim Syntastic](https://github.com/scrooloose/syntastic)

    :   Plugin for the Vim editor providing compile checking.

Discontinued:

-   

    [Mix IDE](https://github.com/ethereum/mix/)

    :   Qt based IDE for designing, debugging and testing solidity smart
        contracts.

-   

    [Ethereum Studio](https://live.ether.camp/)

    :   Specialized web IDE that also provides shell access to a
        complete Ethereum environment.

## Solidity Tools

-   

    [Dapp](https://dapp.readthedocs.io)

    :   Build tool, package manager, and deployment assistant for
        Solidity.

-   

    [Solidity REPL](https://github.com/raineorshine/solidity-repl)

    :   Try Solidity instantly with a command-line Solidity console.

-   

    [solgraph](https://github.com/raineorshine/solgraph)

    :   Visualize Solidity control flow and highlight potential security
        vulnerabilities.

-   

    [evmdis](https://github.com/Arachnid/evmdis)

    :   EVM Disassembler that performs static analysis on the bytecode
        to provide a higher level of abstraction than raw EVM
        operations.

-   

    [Doxity](https://github.com/DigixGlobal/doxity)

    :   Documentation Generator for Solidity.

## Third-Party Solidity Parsers and Grammars

-   

    [solidity-parser](https://github.com/ConsenSys/solidity-parser)

    :   Solidity parser for JavaScript

-   

    [Solidity Grammar for ANTLR 4](https://github.com/federicobond/solidity-antlr4)

    :   Solidity grammar for the ANTLR 4 parser generator

## Language Documentation

On the next pages, we will first see a
[simple smart contract ](./introduction-to-smart-contracts.md#simple-smart-contract-) written in Solidity followed by the basics about
[blockchains ](./introduction-to-smart-contracts.md#blockchains-) and the
[ethereum virtual machine ](./introduction-to-smart-contracts.md#ethereum-virtual-machine-).

The next section will explain several *features* of Solidity by giving
useful [example contracts ](./solidity-by-example.md#example-contracts-)
Remember that you can always try out the contracts [in your
browser](https://remix.ethereum.org)!

The last and most extensive section will cover all aspects of Solidity
in depth.

If you still have questions, you can try searching or asking on the
[Ethereum Stackexchange](https://ethereum.stackexchange.com/) site, or
come to our [gitter channel](https://gitter.im/ethereum/solidity/).
Ideas for improving Solidity or this documentation are always welcome!

# Contents

------>>>>>>genindex

::: {.toctree maxdepth="2"}
introduction-to-smart-contracts.rst installing-solidity.rst
solidity-by-example.rst solidity-in-depth.rst
security-considerations.rst using-the-compiler.rst metadata.rst
abi-spec.rst julia.rst style-guide.rst common-patterns.rst bugs.rst
contributing.rst frequently-asked-questions.rst
:::
