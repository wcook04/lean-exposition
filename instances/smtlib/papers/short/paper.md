
<!-- passage:front -->
# The SMT-LIB Standard: Version 2.7
<!-- /passage:front -->

<a id="3.1"></a>

## 3.1 Lexicon

<!-- passage:sec-3.1 -->

The syntax rules in this chapter are given directly with respect to streams of lexical tokens from the set defined in this section. The whole set of concrete syntax rules is also available for easy reference in Appendix B. SMT-LIB source files consist of Unicode characters in any 8-bit encoding, such as UTF- 8. Most lexical tokens defined below are limited to US-ASCII printable characters, namely, characters 32dec to 126dec . The remaining printable characters, mostly used for non-English alphabet letters (characters 128dec and beyond), are allowed in string literals, quoted symbols, and comments. A comment is any character sequence not contained within a string literal or a quoted sym- bol (see later) that begins with the semi-colon character ; and ends with the first subsequent

line-breaking character, i.e., 10dec or 13dec . Both comments and consecutive white space char- acters occurring outside a string literal or a symbol (see later) are considered whitespace. The only lexical function of whitespace is to break the source text into tokens.1 The lexical tokens of the language are the parenthesis characters ( and ), the elements of the syntactic categories ⟨numeral ⟩ , ⟨decimal ⟩ , ⟨hexadecimal ⟩ , ⟨binary ⟩ , ⟨string ⟩ , ⟨symbol ⟩ , ⟨keyword ⟩ , as well as a number of reserved words, all defined below together with a few auxil- iary syntactic categories.

White Space Characters. A ⟨white\_space\_char ⟩ is one of the following characters: 9dec (tab), 10dec (line feed), 13dec (carriage return), and 32dec (space).

Printable Characters. A ⟨printable\_char ⟩ is any character from 32dec to 126dec (US-ASCII) and from 128dec on.2

Digits. A ⟨digit ⟩ is any character from 48dec to 57dec (0 through 9)

Letters. A ⟨letter ⟩ is any character from 65dec to 90dec (English alphabet letters A through Z) and from 97dec to 122dec (English alphabet letters a through z).( 3 )

Numerals. A ⟨numeral ⟩ is the digit 0 or a non-empty sequence of digits not starting with 0 .

Decimals. A ⟨decimal ⟩ is a token of the form ⟨numeral ⟩.0∗ ⟨numeral ⟩ .

Hexadecimals. A ⟨hexadecimal ⟩ is a non-empty case-insensitive sequence of digits and letters from A to F preceded by the (case sensitive) characters \#x .

Binaries. A ⟨binary ⟩ is a non-empty sequence of the characters 0 and 1 preceded by the char- acters \#b .

String literals. A ⟨string ⟩ (literal) is any sequence of characters from ⟨printable\_char ⟩ or ⟨white\_space\_char ⟩ delimited by the double quote character " (34dec ). The character " can itself occur within a string literal only if duplicated. In other words, after an initial " that starts a literal, a lexer should treat the sequence "" as an escape sequence denoting a single occurrence of " within the literal.

SMT-LIB string literals are akin to raw strings in certain programming languages. How- ever, they have only one escape sequence: "" . This means, for example and in contrast to most programming languages, that within a ⟨string ⟩ the character sequences \\n, \\012, \\x0A, and \\u0008 are not escape sequences (all denoting the new line character), but regular sequences denoting their individual characters.( 4 )

Reserved words. The language uses a number of reserved words, sequences of printable char- acters that are to be treated as individual tokens. The basic set of reserved words consists of the following:

Additionally, each command name in the scripting language defined in Section 3.11 (set-logic, set-option, . . . ) is also a reserved word.( 5 ) The syntactic category ⟨reserved ⟩ denotes any reserved word.

Symbols. A ⟨symbol ⟩ is either a simple symbol or a quoted symbol. A simple symbol is any non-empty sequence of elements of ⟨letter ⟩ and ⟨digit ⟩ and the characters \~ ! @ \$ % ^ & \* \_ - + = \< \> . ? /

that does not start with a digit and is not a reserved word.3

A quoted symbol is any sequence of whitespace characters and printable characters that starts and ends with \| and does not contain \| or \\ .( 6 )

Symbols are case sensitive. They are used mainly as operators or identifiers. Conven- tionally, arithmetic characters and the like are used, individually or in combination, as operator names; in contrast, alpha-numeric symbols, possibly with punctuation char- acters and underscores, are used as identifiers. But, as in LISP, this usage is only rec- ommended (for human readability), not prescribed. For additional flexibility, arbitrary sequences of whitespace and printable characters (except for \| and \\) enclosed in verti- cal bars are also allowed as symbols. Following Common Lisp’s conventions, enclosing a simple symbol in vertical bars does not produce a new symbol. This means for instance that abc and \|abc\| are the same symbol. Simple symbols starting with the character @ or . are reserved for solver use.4 Solvers can use them respectively as identifiers for abstract values and solver-generated function symbols other than abstract values.

Keywords. A ⟨keyword ⟩ is a token of the form :⟨simple\_symbol ⟩ . Elements of this category have a special use in the language. They are used as attribute names or option names (see later).
<!-- /passage:sec-3.1 -->

<a id="3.2"></a>

## 3.2 S-expressions

<!-- passage:sec-3.2 -->

An S-expression is either a non-parenthesis token or a (possibly empty) sequence of S-ex- pressions enclosed in parentheses. Every syntactic category of the SMT-LIB language is a specialization of the category ⟨s\_expr ⟩ defined by the production rules below.

⟨spec\_constant ⟩ ::= ⟨numeral ⟩ \| ⟨decimal ⟩ \| ⟨hexadecimal ⟩ \| ⟨binary ⟩ \| ⟨string ⟩

⟨s\_expr ⟩ ::= \| ⟨spec\_constant ⟩ \| ⟨symbol ⟩ \| ⟨reserved ⟩ \| ⟨keyword ⟩ ( ⟨s\_expr ⟩∗ )
<!-- /passage:sec-3.2 -->

<a id="3.3"></a>

## 3.3 Identifiers

<!-- passage:sec-3.3 -->

Identifiers are used mostly as function and sort symbols. When defining certain SMT-LIB theories it is convenient to have indexed identifiers as well. Instead of having a special token syntax for that, indexed identifiers are defined more systematically as the application of the reserved word \_ to a symbol and one or more indices. Indices can be numerals or symbols.( 7 )

⟨index ⟩ ::= ⟨numeral ⟩ \| ⟨symbol ⟩

⟨identifier ⟩ ::= ⟨symbol ⟩ \| ( \_ ⟨symbol ⟩ ⟨index ⟩+ )
<!-- /passage:sec-3.3 -->

<a id="3.4"></a>

## 3.4 Attributes

<!-- passage:sec-3.4 -->

Several syntactic categories in the language contain attributes. These are generally pairs con- sisting of an attribute name and an associated value, although attributes with no value are also allowed. Attribute names belong to the ⟨keyword ⟩ category. Attribute values are in general S- expressions other than keywords, although most predefined attributes use a more restricted category for their values.

⟨attribute\_value ⟩ ::= ⟨spec\_constant ⟩ \| ⟨symbol ⟩ \| ( ⟨s\_expr ⟩∗ )

⟨attribute ⟩ ::= ⟨keyword ⟩ \| ⟨keyword ⟩ ⟨attribute\_value ⟩
<!-- /passage:sec-3.4 -->

<a id="3.5"></a>

## 3.5 Sorts

<!-- passage:sec-3.5 -->

A major subset of the SMT-LIB language is the language of well-sorted terms, used to represent logical expressions. Such terms are typed, or sorted in first-order logic terminology; that is, each is associated with a (unique) sort. The set of sorts consists itself of sort terms. In essence, a sort is a sort symbol, a sort parameter, or a sort symbol applied to a sequence of sort terms. Syntactically, a sort symbol can be either the distinguished symbol Bool or any ⟨identifier ⟩ . A sort parameter can be any ⟨symbol ⟩ (which in turn, is an ⟨identifier ⟩ ).

⟨sort ⟩ ::= ⟨identifier ⟩ \| ( ⟨identifier ⟩ ⟨sort ⟩+ )
<!-- /passage:sec-3.5 -->

<a id="3.6"></a>

## 3.6 Terms and Formulas

<!-- passage:sec-3.6 -->

Abstractly, terms are constructed out of constant symbols in the ⟨spec\_constant ⟩ category (numerals, decimals, strings, etc.), variables, function symbols, five kinds of binders (introduced by the reserved words lambda, let, forall, exists, and match), and an annotation operator: the reserved word !. In its simplest form, a term is a special constant symbol, a variable, a function symbol, or the application of a function symbol to one or more terms. More complex terms include one or more binders. Concretely, a variable can be any ⟨symbol ⟩ , while a function symbol can be any ⟨identifier ⟩ (i.e., a symbol or an indexed symbol). As a consequence, contextual information is needed during parsing to know whether an identifier is to be treated as a variable or a function sym- bol. For variables, this information is provided by the binders let, lambda, forall, exists, and match, which are the only mechanism to introduce variables. Function symbols, in con- trast, are predefined, as explained later. Recall that every function symbol f is separately associated with one or more ranks, each specifying the sorts of f ’s arguments and result. To simplify sort checking, a function symbol in a term can be annotated with one of its result sorts τ. Such an annotated function symbol is a qualified identifier of the form (as f τ).

⟨qual\_identifier ⟩ ::= ⟨identifier ⟩ \| ( as ⟨identifier ⟩ ⟨sort ⟩ )

⟨var\_binding ⟩ ::= ( ⟨symbol ⟩ ⟨term ⟩ )

⟨sorted\_var ⟩ ::= ( ⟨symbol ⟩ ⟨sort ⟩ )

⟨symbol\_⟩ ::= ⟨symbol ⟩ \| \_

⟨pattern ⟩ ::= ⟨symbol\_⟩ \| ( ⟨symbol ⟩ ⟨symbol\_⟩+ )

⟨match\_case ⟩ ::= ( ⟨pattern ⟩ ⟨term ⟩ )

⟨spec\_constant ⟩ ⟨qual\_identifier ⟩ ( ⟨qual\_identifier ⟩ ⟨term ⟩+ ) ( let ( ⟨var\_binding ⟩+ ) ⟨term ⟩ ) ( lambda ( ⟨sorted\_var ⟩+ ) ⟨term ⟩ ) ( forall ( ⟨sorted\_var ⟩+ ) ⟨term ⟩ ) ( exists ( ⟨sorted\_var ⟩+ ) ⟨term ⟩ ) ( match ⟨term ⟩ ( ⟨match\_case ⟩+ ) ) ( ! ⟨term ⟩ ⟨attribute ⟩+ )
<!-- /passage:sec-3.6 -->

<a id="3.6.1"></a>

## 3.6.1 Variable Binders

<!-- passage:sec-3.6.1 -->

Variables are introduced by means of one of the five binders. Each binder allows the intro- duction of one or more variables with local scope.

Lambda. This binder corresponds to the abstraction binder of higher-order logic. It takes a non-empty list of variables, which abbreviates a sequential nesting of lambda abstractions. Specifically, a term of the form

Exists and forall quantifiers. These binders correspond to the usual universal and existential quantifiers of first-order logic, except that each variable they quantify is also associated with a sort. Both binders have a non-empty list of variables, which abbreviates a sequential nesting of quantifiers. Specifically, a formula of the form

Match. Similarly to pattern matching statements in functional programming languages or in certain interactive theorem provers, the match binder is used to perform pattern matching on values of an algebraic data type (see Section 4.2.3). It has the form

where t is a term of some datatype sort δ and, for each i = 1, . . . , m + 1, pi is a pattern for δ, and ti a term of some sort τ. A pattern p in turn is either a variable x of sort δ, the wildcard \_, a nullary constructor c of δ, or a term of the form (c x1 · · · xk ), where c is a constructor of δ of rank τ1 · · · τk δ with k \> 0, and x1 , . . . , xk are distinct variables of respective sort τ1 , . . . , τk .( 8 ) An exception is the wildcard \_ which can only occur in place of one or more of the variables x1 , . . . , xk . This variable acts as a wildcard, with each occurrence matching any term of any sort, hence effectively behaving as a fresh variable. The list p1 , . . . pm+1 may contain more than one pattern with the same constructor or more than one pattern consisting of a variable.( 9 ) However, it must contain a pattern consisting of a variable, unless every constructor of δ occurs in one of the patterns.( 10 ) The recommended choice for a single variable pattern is \_, when the variable is not used in the corresponding return term.( 11 ) The term ti in (3.6) can contain free occurrences of the variables occurring in pattern pi , if any. The scope of those variables is the term ti .

Remark 5 (No nested patterns). Nested patterns, where the arguments of a constructor can be themselves non-variable patterns, are not allowed.( 12 ) This implies in particular that in a pattern of the form (c s1 · · · sk ), where s1 , . . . , sk are symbols, those symbols are always to be parsed as variables.

The reserved word \_ is used both to construct indexed terms and as a wildcard in match patterns.
<!-- /passage:sec-3.6.1 -->

<a id="3.6.3"></a>

## 3.6.3 Well-sortedness requirements

<!-- passage:sec-3.6.3 -->

Remark 8. A term of the form (as f τ) is allowed even if the symbol f is non-ambiguous, as long as τ matches the return sort of f .
<!-- /passage:sec-3.6.3 -->

<a id="3.6.4"></a>

## 3.6.4 Annotations

<!-- passage:sec-3.6.4 -->

Every term t can be optionally annotated with one or more attributes α1 , . . . , αn using the wrapper expression (! t α1 · · · αn ). Term attributes have no logical meaning—semantically, (! t α1 · · · αn ) is equivalent to t—but they are a convenient mechanism for adding meta- logical information for SMT solvers.
<!-- /passage:sec-3.6.4 -->

<a id="3.11"></a>

## 3.11 Scripts are sequences of commands

<!-- passage:sec-3.11 -->

Scripts are sequences of commands. In line with the LISP-like syntax, all commands look like LISP-function applications, with a command name applied to zero or more arguments. To facilitate processing, each command takes a constant number of arguments, although some of these arguments can be (parenthesis-delimited) lists of variable length. The full list of commands is provided in Figure 3.7. The intended use of scripts is to communicate with an SMT-solver in a read-eval-print loop: until a termination condition occurs, the solver reads the next command, acts on it, outputs a response, and repeats. Possible responses vary from a single symbol to a list of attributes, to complex expressions like proofs. The command set-option takes as an argument expressions of the syntactic category ⟨option ⟩ , which have the same form as attributes with values. Options with the predefined keywords listed in Figure 3.8 have a prescribed usage and semantics. Additional, solver- specific options are also allowed. The command get-info takes as argument expressions of the syntactic category ⟨info\_flag ⟩ which are flags with the same form as keywords. The standard flags listed in Figure 3.9 have

⟨sort\_dec ⟩ ::= ( ⟨symbol ⟩ ⟨numeral ⟩ )

⟨selector\_dec ⟩ ::= ( ⟨symbol ⟩ ⟨sort ⟩ )

⟨constructor\_dec ⟩ ::= ( ⟨symbol ⟩ ⟨selector\_dec ⟩∗ )

⟨datatype\_dec ⟩ ::= ( ⟨constructor\_dec ⟩+ ) \| ( par ( ⟨symbol ⟩+ ) ( ⟨constructor\_dec ⟩+ ) )

⟨function\_dec ⟩ ::= ( ⟨symbol ⟩ ( ⟨sorted\_var ⟩∗ ) ⟨sort ⟩ )

⟨function\_def ⟩ ::= ⟨symbol ⟩ ( ⟨sorted\_var ⟩∗ ) ⟨sort ⟩ ⟨term⟩

( assert ⟨term ⟩ ) ( check-sat ) ( check-sat-assuming ( ⟨term ⟩∗ ) ) ( declare-const ⟨symbol ⟩ ⟨sort ⟩ ) ( declare-datatype ⟨symbol ⟩ ⟨datatype\_dec ⟩ ) ( declare-datatypes ( ⟨sort\_dec ⟩ n+1 ) ( ⟨datatype\_dec ⟩ n+1 ) ) ( declare-fun ⟨symbol ⟩ ( ⟨sort ⟩∗ ) ⟨sort ⟩ ) ( declare-sort ⟨symbol ⟩ ⟨numeral ⟩ ) ( declare-sort-parameter ⟨symbol ⟩ ) ( define-const ⟨symbol ⟩ ⟨sort ⟩ ⟨term ⟩ ) ( define-fun ⟨function\_def ⟩ ) ( define-fun-rec ⟨function\_def ⟩ ) ( define-funs-rec ( ⟨function\_dec ⟩ n+1 ) ( ⟨term ⟩ n+1 ) ) ( define-sort ⟨symbol ⟩ ( ⟨symbol ⟩∗ ) ⟨sort ⟩ ) ( echo ⟨string ⟩ ) ( exit ) ( get-assertions ) ( get-assignment ) ( get-info ⟨info\_flag ⟩ ) ( get-model ) ( get-option ⟨keyword ⟩ ) ( get-proof ) ( get-unsat-assumptions ) ( get-unsat-core ) ( get-value ( ⟨term ⟩+ ) ) ( pop ⟨numeral ⟩ ) ( push ⟨numeral ⟩ ) ( reset ) ( reset-assertions ) ( set-info ⟨attribute ⟩ ) ( set-logic ⟨symbol ⟩ ) ( set-option ⟨option ⟩ )

⟨script ⟩ ::= ⟨command ⟩∗

:diagnostic-output-channel ⟨string ⟩ :global-declarations ⟨b\_value ⟩ :interactive-mode ⟨b\_value ⟩ :print-success ⟨b\_value ⟩ :produce-assertions ⟨b\_value ⟩ :produce-assignments ⟨b\_value ⟩ :produce-models ⟨b\_value ⟩ :produce-proofs ⟨b\_value ⟩ :produce-unsat-assumptions ⟨b\_value ⟩ :produce-unsat-cores ⟨b\_value ⟩ :random-seed ⟨numeral ⟩ :regular-output-channel ⟨string ⟩ :reproducible-resource-limit ⟨numeral ⟩ :verbosity ⟨numeral ⟩ ⟨attribute ⟩

:all-statistics \| :assertion-stack-levels \| :authors :error-behavior \| :name \| :reason-unknown :version \| ⟨keyword ⟩

a prescribed usage and semantics. Additional, solver-specific flags are also allowed. Exam- ples of the latter might be, for instance, flags such as :time and :memory, referring to used resources, or :decisions, :conflicts, and :restarts, referring to typical statistics for current SMT solvers. For more on error behavior, the meanings of the various options and info names, and the semantics of the various commands, see Chapter 4. We highlight a few salient points here and provide a couple of examples.
<!-- /passage:sec-3.11 -->

<a id="appendix-b"></a>

## Appendix B Concrete Syntax

<!-- passage:sec-appendix-b -->

Predefined symbols These symbols have a predefined meaning in Version 2.7. Note that they are not reserved words. For instance, they could also be used in principle as user-defined sort or function symbols in scripts. Bool continued-execution error false immediate-exit incomplete logic memout sat success theory true unknown unsupported unsat

⟨white\_space\_char ⟩ ::= 9dec \| 10dec \| 13dec \| 32dec

⟨printable\_char ⟩ ::= 32dec \| · · · \| 126dec \| 128dec \| · · · \| 255dec

⟨digit ⟩ ::= 0 \| ··· \| 9

⟨letter ⟩ ::= A \| ··· \| Z \| a \| ··· \| z

⟨numeral ⟩ ::= 0 \| a non-empty sequence of digits not starting with 0

⟨decimal ⟩ ::= ⟨numeral ⟩.0∗ ⟨numeral ⟩

⟨hexadecimal ⟩ ::= \#x followed by a non-empty sequence of digits and letters from A to F , capitalized or not

⟨binary ⟩ ::= \#b followed by a non-empty sequence of 0 and 1 characters

⟨string ⟩ ::= sequence of whitespace and printable characters in double quotes with escape sequence ""

⟨simple\_symbol ⟩ ::= a non-empty sequence of letters, digits and the characters

⟨symbol ⟩ ::= \| ⟨simple\_symbol ⟩ a sequence of whitespace and printable characters that starts and ends with \| and does not otherwise include \| or \\

⟨keyword ⟩ ::= :⟨simple\_symbol ⟩

⟨pattern⟩ ::= ⟨symbol\_⟩ \| ( ⟨symbol ⟩ ⟨symbol\_⟩+ )
<!-- /passage:sec-appendix-b -->

