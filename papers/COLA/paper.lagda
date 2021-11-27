\documentclass[review]{elsarticle}

\usepackage{lineno,hyperref}
\modulolinenumbers[5]



\usepackage{booktabs} % For formal tables
\usepackage[utf8x]{inputenc}
\usepackage{ucs}
\usepackage{graphicx}
\usepackage{amsmath,amsthm}
\usepackage{amssymb}
\usepackage{url}
\usepackage{stmaryrd}
\usepackage{ifpdf}
\usepackage{mathtools}
\usepackage{semantic}

\ifpdf
\usepackage{hyperref}
\fi
\usepackage{float}
\usepackage{proof}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% color formatting stuff %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newtheorem{Lemma}{Lemma}
\newtheorem{Theorem}{Theorem}
\theoremstyle{definition}
\newtheorem{Example}{Example}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX stuff  %%
%%%%%%%%%%%%%%%%%%%%


%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%subst numeral a = "\Con{" a "}"

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\Con}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}

%subst comment a = "\orange{\texttt{--" a "}}"



\journal{Journal of Computer Languages}


%% `Elsevier LaTeX' style
\bibliographystyle{elsarticle-num}
%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{frontmatter}

\title{An Intrinsically-Typed Solution for the\\ List-Machine Benchmark}

\author{Samuel Feitosa}
\ead{samuel.feitosa@@ifsc.edu.br}
\address{%
  Departamento de Informática - Instituto Federal de Santa Catarina \\
  Caçador - Santa Catarina - Brazil
}

\author{Rodrigo Ribeiro}
\ead{rodrigo.ribeiro@@ufop.edu.br}
\address{
  Prog. Pós Graduação em Ciência da Computação - Universidade Federal de Ouro Preto \\
  Ouro Preto - Minas Gerais - Brazil}


%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract          %%
%%%%%%%%%%%%%%%%%%%%%%%

\begin{abstract}
Formal models are important tools in the programming language research
community. However, such models are full of intricacies and, due to that,
they are subject to subtle errors. Such failures motivated the usage of
tools to ensure the correctness of these formalisms. One way to eliminate
such errors is to encode models in a dependently-typed language in order
to ensure its ``correctness-by-construction''. In this paper, we use this
idea to build a verified interpreter for the list-machine benchmark in the
Agda programming language, comparing the results with formalizations developed
by Appel et. al. We formalize the 14 tasks of the benchmark
using roughly 14\% of LOC compared to a Twelf solution, and 47\% of LOC
compared to a Coq solution, even without the use of proof automation. We also
describe a solution to the second version of the benchmark and compare it with
Appel's et. al. Coq-based solution.
\end{abstract}


\begin{keyword}
Dependent types, formal semantics, Agda
\end{keyword}

\end{frontmatter}

\linenumbers

%format . = "."
%format Set = "\D{Set}"
%format Set0 = Set "_{\D{0}}"
%format Set1 = Set "_{\D{1}}"
%format List = "\D{List}"
%format [] = "\Con{\lbrack\:\rbrack}"
%format , = "\red{,}\,"
%format Nat = "\D{\mathbb{N}}"
%format zero = "\Con{zero}"
%format succ = "\Con{suc}"
%format id = "\F{id}"
%format o = "\F{\circ}"
%format Vec = "\D{Vec}"
%format :: = "\Con{::}"
%format _::_ = "\Con{\_::\_}"


%%%%%%%%%%%%%%%%%%%%%%%
%% Introduction      %%
%%%%%%%%%%%%%%%%%%%%%%%



\section{Introduction}

The development of a new programming language design, linguistic construct,
or type system involves a careful formalization in order to express
its core ideas in a concise way. However, such models have many details
and complexities which can hinder its correctness assurances.
Because of such problems, the programming languages research community
started to use tools, like proof assistants~\cite{Stump16,Chlipala13},
and benchmark problems to validate them and stress its suitability for
such specification tasks~\cite{Aydemir05,Pientka18,Appel07}.

A popular approach for specifying formal semantics is the
use of definitional interpreters, which represents the meaning of a
programming language as an interpreter written in some
meta-language~\cite{Reynolds72}. A major advantage of such approach
is the possibility to validate the semantics through execution.
Recently, definitional interpreters were used for formalizing type
soundness theorems for some advanced typing features~\cite{Amin17},
and the semantics of imperative programming languages, in such a way the static
semantics is ensured by a dependently-typed
syntax\footnote{Also known as intrinsically-typed.}\cite{Poulsen18}.
In this work, we follow Poulsen et. al. by using an intrinsically-typed
representation to build a definitional interpreter for a low-level virtual
machine, developed by Appel et. al., as a benchmark problem closer to
real-world implementations such as typed assembly languages~\cite{CraryM99} and
proof-carrying code~\cite{Necula97}.

In this work, we extend our previous SBLP 2020 paper~\cite{Feitosa2020} by including support to
indirect jumps, as specified in the version 2.0 of the list
machine benchmark~\cite{AppelDL12}. We provide detailed explanations of the needed
changes on the machine syntax, type system and interpreter to accommodate this extension, which
allows the handling of more complex control flow structures, like the call/return model of function calls.

Let us summarize our contributions. %More specifically, we contribute:

\pagebreak

\begin{itemize}
  \item We show how all the details of the list-machine type system
        can be encoded in a dependently-typed syntax setting, which avoids, by construction,
        the presence of stuck states in its definitional interpreter.
  \item We provide a provably correct implementation for testing the subtyping
        relation and to calculate the least common supertype of two input
        types for the machine registers.
  \item We provide a correct-by-construction implementation of a type-checker for the
        list-machine programs. Our type-checker produces, as a result, an intrinsically-typed
        representation of the machine code.
  \item We compare the results of an intrinsic approach encoded in Agda with extrinsic
        formalizations encoded in Twelf and Coq. We show that such intrinsic encoding avoids
        unnecessary repetitions and provides some properties for free.
  \item We provide a detailed discussion on the necessary modifications to the type system,
        type checker and interpreter to support indirect jumps.
\end{itemize}

The rest of this paper is organized as follows: Section~\ref{sec:agda} presents an overview of
the Agda programming language and Section~\ref{sec:syntax}
gives a brief explanation about the encoding of dependently-typed syntax. Section~\ref{sec:list}
reviews the list-machine benchmark and presents its syntax and type system.
We describe the intrinsically-typed representation for the list-machine, as well as
the subtyping relation, and the least common supertype algorithm in Section~\ref{sec:typing}.
Section~\ref{sec:semantics} briefly discusses the list-machine semantics and
then proceeds with its realization as a definitional interpreter.
The type-checking algorithm is presented in Section~\ref{sec:typechecker}.
Section~\ref{sec:indirect} describes the necessary modifications in our formalization to
support indirect jumps, as proposed in the version 2.0 of the list machine benchmark.
Section~\ref{sec:comparison}
compares the presented formalization in Agda with Coq and Twelf encodings. Related work is
discussed in Section~\ref{sec:related}, and Section~\ref{sec:conclusion} concludes.

All the source code in this article has been formalized in Agda
version 2.6.1 using the Standard Library 1.3. All source code produced,
including the \LaTeX~source of this article, are available
on-line~\cite{list-rep}.


%%%%%%%%%%%%%%%%%%%%%%%
%% Overview of Agda  %%
%%%%%%%%%%%%%%%%%%%%%%%

\section{An overview of the Agda programming language}\label{sec:agda}


%format String = "\D{String}"
%format Bool = "\D{Bool}"
%format forall = "\D{\forall}"
%format ℕ = "\D{\mathbb{N}}"

Agda is a dependently-typed functional programming language based on
Martin-L\"of intuitionistic type theory~\cite{Lof98}.  Function types
and an infinite hierarchy of types of types, |Set l|, where |l| is a
natural number, are built-in. Everything else is a user-defined
type. The type |Set|, also known as |Set0|, is the type of all
``small'' types, such as |Bool|, |String| and |List Bool|.  The type
|Set1| is the type of |Set| and ``others like it'', such as |Set -> Bool|,
|String -> Set|, and |Set -> Set|. We have that |Set l| is an
element of the type |Set (l+1)|, for every $l \geq 0$. This
stratification of types is used to keep Agda consistent as a logical
theory~\cite{Sorensen2006}.

An ordinary (non-dependent) function type is written |A -> B| and a
dependent one is written |(x : A) -> B|, where type |B| depends on
|x|, or |forall (x : A) -> B|. Agda allows the definition of \emph{implicit
parameters}, i.e.,  parameters whose values can be inferred from the
context, by surrounding them in curly braces: |forall {x : A} -> B|. To
avoid clutter, we'll omit implicit arguments from the source code
presentation. The reader can safely assume that every free variable in
a type is an implicit parameter.

As an example of Agda code, consider the following data type of
length-indexed lists, also known as vectors.

 \begin{spec}
   data Nat : Set where
     zero : Nat
     succ : Nat -> Nat

   data Vec (A : Set) : Nat -> Set where
     []  : Vec A zero
     _::_ : forall {n} -> A -> Vec A n -> Vec A (succ n)
 \end{spec}

%format head = "\F{head}"

Constructor |[]| builds empty vectors. The cons-operator (|_::_|)\footnote{Agda supports the definition of mixfix operators.
We can use underscores to mark arguments positions.}
inserts a new element in front of a vector of $n$ elements (of type
|Vec A n|) and returns a value of type |Vec A (succ n)|. The
|Vec| datatype is an example of a dependent type, i.e., a type
that uses a value (that denotes its length). The usefulness of
dependent types can be illustrated with the definition of a safe list
head function: |head| can be defined to accept only non-empty
vectors, i.e.,~values of type |Vec A (succ n)|.
\begin{spec}
  head : Vec A (succ n) -> A
  head (x :: xs) = x
\end{spec}

In |head|'s definition, constructor |[]| is not used. The
Agda type-checker can figure out, from |head|'s parameter type,
that argument |[]| to |head| is not type-correct.

%format _==_ = "\D{\_ \equiv \_}"
%format == = "\D{\equiv}"
%format refl = "\Con{refl}"
%format proj₁ = "\F{\pi_1}"
%format proj₂ = "\F{\pi_2}"
%format Fin   = "\D{Fin}"
%format lookup = "\F{lookup}"


Another useful data type is the finite type,
|Fin|\footnote{Note that Agda supports the overloading of
data type constructor names. Constructor |zero| can refer to
type |Nat| or |Fin|, depending on the context where the name
is used.}, which is defined in Agda's standard library as:
\begin{spec}
  data Fin : Nat -> Set where
    zero : forall {n} -> Fin (succ n)
    succ : forall {n} -> Fin n -> Fin (succ n)
\end{spec}
Type |Fin n| has exactly |n| inhabitants
(elements), i.e., it is isomorphic to the set $\{0,...,n - 1\}$.
An application of such type is to define a safe vector
lookup function, which avoids the access of invalid positions.
\begin{spec}
  lookup : forall {A n} -> Fin n -> Vec A n -> A
  lookup zero (x :: _) = x
  lookup (succ idx) (_ :: xs) = lookup idx xs
\end{spec}
Thanks to the propositions-as-types principle,\footnote{It is also known as
Curry-Howard ``isomorphism''~\cite{Sorensen2006}.} we can interpret
types as logical formulas and terms as proofs. An example is the
representation of equality as the following Agda type:

\begin{spec}
  data _==_ {l}{A : Set l}(x : A) : A -> Set where
    refl : x == x
\end{spec}

%format not = "\F{\neg}"
%format Dec = "\D{Dec}"
%format yes = "\Con{yes}"
%format no  = "\Con{no}"
%format Even = "\Con{Even}"
%format Odd = "\Con{Odd}"
%format Parity = "\D{Parity}"
%format parity = "\F{parity}"
%format natToBin = "\F{natToBin}"
%format false = "\Con{false}"
%format true = "\Con{true}"
%format + = "\F{+}"
%format ++ = "\F{++}"
%format Bot = "\D{\bot}"
%format All = "\D{All}"
%format foo = "\F{foo}"
%format P   = "\D{P}"
%format plus-comm = "\F{plus\textrm{-}comm}"
%format rewrite = "\mathkw{rewrite}"
This type is called propositional equality. It defines that there is
a unique evidence for equality, constructor |refl| (for reflexivity),
which asserts that the only value equal to |x| is itself.


Dependently typed pattern matching is built by using the so-called
|with| construct, that allows for matching intermediate
values~\cite{McBride2004}. If the matched value has a dependent type,
then its result can affect the form of other values. For example,
consider the following code that defines a type for natural number
parity. If the natural number is even, it can be represented as the
sum of two equal natural numbers; if it is odd, it is equal to one
plus the sum of two equal values. Pattern matching on a value of
|Parity n| allows to discover if $n = j + j$ or $n = S (k + k)$,
for some $j$ and $k$ in each branch of |with|.  Note that the
value of $n$ is specialized accordingly, using information ``learned''
by the type-checker.
\begin{spec}
data Parity : Nat -> Set where
   Even : forall {n : Nat} -> Parity (n + n)
   Odd  : forall {n : Nat} -> Parity (S (n + n))

parity : (n : Nat) -> Parity n
parity = -- definition omitted

natToBin : Nat -> List Bool
natToBin zero = []
natToBin k with (parity k)
   natToBin (j + j)     | Even = false :: natToBin j
   natToBin (succ (j + j)) | Odd  = true  :: natToBin j
\end{spec}
A important application of Agda's dependently-typed pattern matching is
to rewrite an equality. As an example, consider the following code which
postulates the commutativity of natural number addition and a predicate
over natural numbers, |P|.

\begin{spec}
postulate plus-comm : (a b : ℕ) → a + b == b + a
postulate P : ℕ → Set

foo : (a b : Nat) → P (a + b) → P (b + a)
foo a b t with   a + b  | plus-comm a b
foo a b t    | .(b + a) | refl = t
\end{spec}
Function |foo| uses the |with| construct to pattern-match on the equality produced
by |plus-comm|,  |a + b == b + a|. Since the propositional equality type has only one
constructor, |refl|, matching over it makes Agda type checker to replace
all occurrences of |a + b| to |b + a| in the current equation context. We can notice
this by the use of the \empth{dotted-pattern} |.(b + a)| which indicates that the
only way that this equation is correct is when the first result of the |with| construct
is |b + a|. The use of dependent pattern matching to rewrite equalities in functions is
so common in Agda that the language provides a syntax sugar that simplifies such structure.
The |rewrite| construct allows the substitution of an equality in all values in a certain
equation. The |foo| function could be represented more concisely, using |rewrite|, as:
\begin{spec}
foo : (a b : ℕ) → P (a + b) → P (b + a)
foo a b t rewrite plus-comm a b = t
\end{spec}

Another inductive predicate used in our formalization is the type |All P xs| which
ensures that all elements of a vector |xs| satisfy a predicate |P : A -> Set|.
\begin{spec}
  data All (P : A -> Set) : Vec A n ->  Set where
    [] : All P []
    _::_ : forall {x xs} -> P x -> All P xs -> All P (x :: xs)
\end{spec}
The first constructor specifies that |All P| holds for the empty vector and
constructor |_::_| builds a proof of |All P (x :: xs)| from proofs of
|P x| and |All P xs|. Since this type has the same structure of vectors,
some functions on |Vec| have similar definitions for type |All|. As an example
used in our formalization, consider the function |lookup|, which extracts a
proof of |P| for the element at position |v : Fin n| in a |Vec|:
\begin{spec}
   lookup : {xs : Vec A n} -> Fin n -> All P xs -> P x
   lookup zero (px :: _) = px
   lookup (succ idx) (_ :: pxs) = lookup idx pxs
\end{spec}



\section{Dependently-typed Syntax}\label{sec:syntax}


An important application of dependent types is to encode programming languages
syntax. The role of dependent types in this domain is to encode programs that
only allow well-typed and well-scoped terms~\cite{Benton2012}. Intuitively, we encode
the static semantics of the object language in the host language AST's
constructor, leaving the responsibility of checking type safety to the
host language type-checker. Before considering our solution to encode list-machine
programs as intrinsically-typed syntax, we review this approach in a reduced example.

Consider the following simple
expression language. For this paper, we assume a basic knowledge of functional
programming and Agda. %\footnote{For further information about Agda, see~\cite{Norell2009,Stump16}.}.

%format Expr = "\D{Expr}"
%format True = "\Con{True}"
%format False = "\Con{False}"
%format Num = "\Con{Num}"
%format _&_ = "\Con{\_\land\_}"
%format _+_ = "\Con{\_+\_}"

\begin{spec}
   data Expr : Set where
      True False : Expr
      Num : Nat -> Expr
      _&_ _+_ : Expr -> Expr -> Expr
\end{spec}

With this data type, we can construct expressions
to denote terms that should not be considered well-typed like
|(Num 1) + True|. Using this approach, we need to specify the static semantics
as another definition, which should consider all possible cases to avoid the
definition of ill-typed terms.

A better approach is to combine the static semantics and language syntax into
a single definition, as shown below.

%format Ty = "\D{Ty}"
%format Natt = "\Con{Nat}"
%format Booll = "\Con{Bool}"
\begin{spec}
   data Ty : Set where
      Natt Booll : Ty

   data Expr : Ty -> Set where
      True False : Expr Booll
      Num : Natt -> Expr Natt
      _&_ : Expr Booll -> Expr Booll -> Expr Booll
      _+_ : Expr Natt -> Expr Natt -> Expr Natt
\end{spec}

In this definition, the |Expr| type is indexed by a value of type |Ty| which
indicates the type of the expression being built. In this approach, Agda's
type system can enforce that only well-typed terms could be written.
%A definition which uses the expression |(Num 1) + True| will be rejected by Agda's type checker automatically.
Agda's type-checker will automatically reject a definition which uses the expression |(Num 1) + True|.

For further information about Agda, see~\cite{Norell2009,Stump16}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% List-machine benchmark %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\section{The List-Machine Benchmark}\label{sec:list}


In this section, we review the syntax, semantics and typing rules for the
list-machine, as originally proposed by Appel et. al.~\cite{AppelDL12}.
The machine is a simple pointer virtual machine where values
are empty lists and cons-cells:
\[
a ::= nil\,\mid\,cons(a_1,a_2)
\]
Throughout this text, the meta-variable $a$ is used to denote an arbitrary value, $v$ denotes a variable
and $l$ a program label. Following common practice, all meta-variables can
appear primed or subscripted. The syntax of the virtual machine instructions are
presented next.
\begin{figure}[H]
\[
\begin{array}{rcll}
  \iota & ::=  & \text{jump }l                       & \text{(jump instruction)}\\
        & \mid & \text{branch-if-nil $v$~$l$}            & \text{(if $v = nil$ goto $l$)}\\
        & \mid & \text{fetch-field $v$ 0 $v'$}       & \text{(fetch the head of $v$ into $v'$)}\\
        & \mid & \text{fetch-field  $v$ 1 $v'$}      & \text{(fetch the tail of $v$ into $v'$)}\\
        & \mid & \text{cons $v_0$ $v_1$ $v'$}        & \text{(make a cons cell in $v'$)} \\
        & \mid & \text{halt}                         & \text{(finishes execution)}\\
        & \mid & \iota_1;\iota_2                             & \text{(sequential composition)}\\
      p & ::=  & l_i \,:\,\iota\,;\,p                    & \text{(program: sequence of blocks)}\\
        & \mid & \text{end}                          & \text{(end of block list)}\\
\end{array}
\]
\centering
\caption{Syntax of list-machine programs}
\label{fig:list-syntax}
\end{figure}
A program is just a sequence of blocks referenced by a unique label.

Each program variable is assigned to a list type (Figure~\ref{fig:type-syntax}), which is used to guarantee the safety of executing
fetch-field instructions that demands non-empty list arguments. In order to express such refinements, types are subject to a
subtyping relation. The meta-variable $\tau$ denotes an arbitrary type.
\begin{figure}[H]
\[
\begin{array}{rcll}
  \tau & ::=  & \text{nil} & \text{(type for empty lists)}\\
       & \mid & \text{list }\tau & \text{(lists whose elements have type $\tau$)}\\
       & \mid & \text{listcons }\tau & \text{(non-empty lists of $\tau$)}\\
\end{array}
\]
\centering
\caption{Type syntax}
\label{fig:type-syntax}
\end{figure}
The notation $\tau \subset \tau'$
denotes the subtyping judgment, which is defined as follows.
\begin{figure}[H]
\[
\begin{array}{c}
  \inference{}
            {\tau\subset \tau}
            [subtype-refl]
  \\ \\
  \inference{}
            {nil \subset list\:\tau}
            [subtype-nil]
  \\ \\
  \inference{\tau \subset \tau'}
            {list\:\tau\subset list\:\tau'}
            [subtype-list]\\ \\
  \multicolumn{3}{c}{
  \inference{\tau \subset \tau'}
            {listcons\:\tau\subset list\:\tau'}
            [subtype-listmixed]} \\ \\
  \multicolumn{3}{c}{
            \inference{\tau \subset \tau'}
            {listcons\:\tau\subset listcons\:\tau'}
            [subtype-listcons]} \\ \\
\end{array}
\]
\centering
\caption{Subtyping relation}
\label{fig:subtyping}
\end{figure}
Basically, the subtyping relation specifies that $nil$ (empty list type) is
subtype of any list type and $listcons\:\tau$ is a subtype of the $list\:\tau$.
The other rules specify that type constructors $list$ and $listcons$ respect
the subtyping relation. The least common supertype $\tau = \tau_1 \sqcup \tau_2$ of
$\tau_1$ and $\tau_2$ is defined as the smallest type such that $\tau_1$ and $\tau_2$
are subtypes of $\tau$.

Following the common practice, the meta-variable $\Gamma$ denotes an
environment binding variable names to their types. Notation $\{\}$ denotes an empty environment, $v : \tau , \Gamma$
denotes the operation of including a new entry for variable $v$ with type $\tau$
in $\Gamma$ and $\Gamma [v := \tau]$ denotes the environment which is identical to $\Gamma$, except
by the entry which associates variable $v$ with type $\tau$.
Subtyping is extended to contexts as follows.
\begin{figure}[H]
\[
\begin{array}{cc}
  \inference{}
            {\Gamma \subset_{env} \{\}}[b1]
  &
  \inference{\tau' \subset \tau & \Gamma' \subset_{env} \Gamma_2}
            {v : \tau' , \Gamma' \subset_{env} v : \tau , \Gamma_2}
            [b2]
\end{array}
\]
\centering
\caption{Subtyping relation for typing contexts.}
\label{fig:subtyping-context}
\end{figure}
The variable $\Pi$ is used to denote \emph{program typings}, i.e. finite mappings between
labels and typing contexts $\Gamma$, where notation $\Pi(l) = \Gamma$ denotes that
$\Gamma$ stores the types of variables on the entry point of the block labeled by $l$.
Using the previously defined notations, the typing rules for the list-machine are defined
as a syntax-directed judgment $\Pi \vdash_{\text{instr}} \Gamma \{ \iota \} \Gamma'$,
which intuitively means that the instruction $\iota$ transforms an input typing environment
$\Gamma$ into an output environment $\Gamma'$ under a fixed program typing $\Pi$. The typing
rules for the list-machine instructions are defined as follows.

The first typing rule we consider is the one for sequencing instructions inside a block. Basically,
the rule just threads the output environment from the first instruction as the input typing for the
second.
\begin{figure}[H]
\[
\inference{\Pi \vdash_{\text{instr}} \Gamma\{ \iota_1 \}\Gamma'\:\:\:\:\:\:\:\:\Pi \vdash_{\text{instr}} \Gamma'\{ \iota_2 \}\Gamma''}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \iota_1 ; \iota_2 \}\Gamma''}[check-instr-seq]
\]
\centering
\caption{Typing rule for instruction sequencing}
\label{fig:typing-seq}
\end{figure}
The type system proposed by Appel et. al.~\cite{AppelDL12} has three rules to deal with each of the possible
types assigned to the branch variable in the current typing context. The first two rules deal with the $list$ and $listcon$
types, specifying that the environment associated to the label $l$, $\Pi(l) = \Gamma_1$, is greater than
$\Gamma[v := nil]$. The third rule applies whenever $\Gamma(v) = nil$ and it also demands that $\Gamma \subset \Pi(l)$.
\begin{figure}[H]
\[
\begin{array}{c}
\inference{\Gamma(v) = \text{list}~\tau\:\:\:\:\:\:\:\:\Pi(l) = \Gamma_1\\
                     \Gamma[v:=\text{nil}]=\Gamma'\:\:\:\:\:\:\:\:\Gamma' \subset_{env} \Gamma_1}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{branch-if-nil}~v~l \}(v: \text{listcons}~\tau,~\Gamma')}
          [check-instr-branch-list]
\\ \\

\inference{\Gamma(v) = \text{listcons}~\tau\:\:\:\:\:\:\:\:\Pi(l) = \Gamma_1\\
           \Gamma[v:=\text{nil}]=\Gamma'\:\:\:\:\:\:\:\:\Gamma' \subset_{env} \Gamma_1}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{branch-if-nil}~v~l \}\Gamma}
          [check-instr-branch-listcons]

\\ \\
\inference{\Gamma(v) = \text{nil}\:\:\:\:\Pi(l) = \Gamma_1\:\:\:\:\Gamma \subset \Gamma_1}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{branch-if-nil}~v~l \}\Gamma}
          [check-instr-branch-nil]
\end{array}
\]
\centering
\caption{Typing rules for branching instructions}
\label{fig:typing-branch}
\end{figure}
Next, we have the \emph{fetch} instructions, which can be used to store the head / tail of a list value in
a variable. Rule \emph{fetch-0} retrieves the head of a value stored in a variable $v$ and \emph{fetch-1}
does the same for the tail. Note that both rules demand that $\Gamma(v) = listcons\:\tau$, for some type
$\tau$.
\begin{figure}[H]
\[
\begin{array}{c}
\inference{\Gamma(v) = \text{listcons}~\tau\:\:\:\:\Gamma[v':=\tau]=\Gamma'}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{fetch-field}~v~0~v' \}\Gamma'}
          [check-instr-fetch-0]
          \\ \\
\inference{\Gamma(v) = \text{listcons}~\tau\:\:\:\:\Gamma[v':=\text{list}~\tau]=\Gamma'}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{fetch-field}~v~1~v' \}\Gamma'}
          [check-instr-fetch-1]
\end{array}
\]
\centering
\caption{Typing rules for field fetching instructions}
\label{fig:typing-fetching}
\end{figure}
The \emph{cons} instruction allows us to build a non-empty list value and this rule uses the least
common supertype operator to check if the result of the operation is really a list type.
\begin{figure}[H]
\[
\inference{\Gamma(v_0) = \tau_0\:\:\:\:\:\:\:\:\Gamma(v_1) = \tau_1 \\
           (\text{list}~\tau_0) \sqcup \tau_1=\text{list}~\tau\:\:\:\:\:\:\:\:\Gamma[v:=\text{listcons}~\tau]=\Gamma'}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{cons}~v_0~v_1~v \}\Gamma'}
          [check-instr-cons]
\]
\centering
\caption{Typing rule for cons instruction}
\label{fig:typing-fetching}
\end{figure}
The final rules deal with the well-formedness of blocks and programs. The typing rules for the \textbf{halt} instruction and
program \textbf{end} are completely trivial. Rule \emph{block-seq} does the typing context threading between sequential
instructions inside a block and rule \emph{block-label} recursively applies the judgment $\vdash_{block}$ on the
input program.
\begin{figure}[H]
\[
\begin{array}{c}
   \inference{}
             {\Pi;\Gamma\vdash_{\text{block}} \textbf{halt}}[check-block-halt]
   \\ \\
   \inference{}
             {\Pi\vdash_{\text{blocks}} \textbf{end}}[check-block-empty]\\ \\

   \inference{\Pi(l)=\Gamma_1\\ \Gamma \subset_{env} \Gamma_1}
             {\Pi;\Gamma\vdash_{\text{block}} \textbf{jump}~l}[check-block-jump]

   \\ \\

   \inference{\Pi\vdash_{\text{instr}} \Gamma\{\iota_1\}\Gamma'\\ \Pi;\Gamma'\vdash_{\text{block}} \iota_2}
             {\Pi;\Gamma\vdash_{\text{block}} \iota_1;\iota_2}[check-block-seq]
 \\ \\

   \inference{\Pi(l)=\Gamma\:\:\:\:\:\:\:\:\Pi;\Gamma\vdash_{\text{block}} \iota\:\:\:\:\:\:\:\:\Pi\vdash_{\text{blocks}} p}
     {\Pi\vdash_{\text{blocks}} l: \iota;~p}[check-blocks-label]
\end{array}
\]
\centering
\caption{Typing rules for program blocks}
\label{fig:typing-block}
\end{figure}
Inspired by the presented typing rules, in the next section, we define an
intrinsically-typed syntax for list-machine programs which allows
only well-typed pro\-grams.

\section{Intrinsically-Typed Syntax}\label{sec:typing}

%format Ty = "\D{Ty}"
%format nil = "\Con{nil}"
%format list = "\Con{list}"
%format listcons = "\Con{listcons}"
%format → = "\rightarrow"
%format ∀ = "\D{\forall}"

In this section we introduce the design choices and the steps we took to represent the
intrinsically-typed syntax for the list-machine benchmark. We present here the Agda
code used in our definitions, not necessarily in a strict lexically-scoped order.

Some definitions and rules have been slightly tweaked so that they are accepted by
the Agda's type-checker. As a design choice, we dropped all names, using
\emph{de Bruijn} indices~\cite{DEBRUIJN72} to represent both \emph{name bindings}
for labels and variables. This way, we guarantee that names are always well-scoped.

We started our formalization by defining a type |Ty|, indicating the possible types
for the list-machine language.

\begin{spec}
data Ty : Set where
  nil       : Ty
  list      : Ty → Ty
  listcons  : Ty → Ty
\end{spec}

We internalize the list-machine type judgments for blocks and instructions in Agda
together with its syntax in such a way that only well-typed terms that satisfy typing
judgments have meaning. This approach makes the AST contain both syntactic and semantic
properties.

In order to be considered well-typed, list-machine programs need to refer
to information from two sources: (1) a type context encoded as a list to store
variable types; and (2) a program context encoded as a vector\footnote{We use the
|Vec| datatype indexed by an |n| which is bound on the module definition and represents
the number of labels in the current program.} of type contexts to represent the types of
the variables on entry to each basic block.

%format Ctx = "\D{Ctx}"
%format PCtx = "\D{PCtx}"

\begin{spec}
Ctx : Set
Ctx = List Ty

PCtx : ℕ → Set
PCtx n = Vec Ctx n
\end{spec}

%format _⊢_⇒_ = "\D{\_\vdash\_\Rightarrow\_}"
%format Block = "\D{Block}"
%format Π = "\V{\Pi}"
%format Γ = "\V{\Gamma}"
%format Γ' = "\V{\Gamma''}"
%format ι = "\V{\iota}"

As we saw in the previous section, the typing rules for the list-machine language were split
into two segments, one for instructions and one for blocks. We define two datatypes (|_⊢_⇒_| and |Block|)
to hold the well-typed terms accordingly, representing each judgment of the static semantics as a
syntactical constructor. In Agda we use \emph{indexed inductive types} to define an intrinsically-typed syntax.
The basic idea is to represent each type system rule as a constructor typed by an output context.
Such a representation scheme makes Agda's type-checker allow only well-typed blocks and
instructions to be created and manipulated.


%Both definitions are \emph{parameterized} by a program context and a typing context, and
%\emph{indexed}\footnote{An index can vary in the result types of the different constructors,
%while a parameter cannot.} by a resulting typing context. The intuition is that, under
%program-typing |Π|, the \emph{Hoare triple} |Γ{ι}Γ'| relates precondition |Γ| to
%postcondition |Γ'|. It is important to note that instead of manipulating syntax directly,
%the meta-program manipulates structures representing the type judgments as well.
%Such
%representation scheme makes the Agda's type-checker allow only well-typed blocks and
%instructions to be created and manipulated.

The representation of instructions is defined as follows.

%format ∈ = "\D{\in}"
%format ⊓ = "\D{\sqcap}"
%format ⊔ = "\D{\sqcup}"
%format ~ = "\D{=}"
%format ∷ = "\Con{::}"
%format ∷= = "\F{::=}"
%format Ctx = "\D{Ctx}"
%format PCtx = "\D{PCtx}"
%format ⊢ = "\D{\vdash}"
%format ⇒ = "\D{\Rightarrow}"
%format ⊂ = "\D{\subset}"
%format [ = "\D{[}"
%format ]= = "\D{]=}"

%format Γ'' = "\V{\Gamma''''}"
%format Γ₁ = "\V{\Gamma_1}"
%format τ = "\V{\tau}"
%format τ = "\V{\tau}"
%format τ' = "\V{\tau''}"
%format τ'' = "\V{\tau''''}"
%format τ₀ = "\V{\tau_0}"
%format τ₁ = "\V{\tau_1}"
%format τ₂ = "\V{\tau_2}"

%format instr-seq = "\Con{instr\textrm{-}seq}"
%format instr-branch-list = "\Con{instr\textrm{-}branch\textrm{-}list}"
%format instr-branch-listcons = "\Con{instr\textrm{-}branch\textrm{-}listcons}"
%format instr-branch-nil = "\Con{instr\textrm{-}branch\textrm{-}nil}"
%format instr-fetch-0-new = "\Con{instr\textrm{-}fetch\textrm{-}0\textrm{-}new}"
%format instr-fetch-0-upd = "\Con{instr\textrm{-}fetch\textrm{-}0\textrm{-}upd}"
%format instr-fetch-1-new = "\Con{instr\textrm{-}fetch\textrm{-}1\textrm{-}new}"
%format instr-fetch-1-upd = "\Con{instr\textrm{-}fetch\textrm{-}1\textrm{-}upd}"
%format instr-cons-new = "\Con{instr\textrm{-}cons\textrm{-}new}"
%format instr-cons-upd = "\Con{instr\textrm{-}cons\textrm{-}upd}"

\begin{spec}
data _⊢_⇒_ (Π : PCtx)(Γ : Ctx) : Ctx → Set where
  instr-seq              : ∀ {Γ' Γ''} → Π ⊢ Γ ⇒ Γ'
                         → Π ⊢ Γ' ⇒ Γ'' → Π ⊢ Γ ⇒ Γ''
  instr-branch-list      : ∀ {τ l Γ'} → (idx : list τ ∈ Γ)
                         → Π [ l ]= Γ' → (idx ∷= nil) ⊂ Γ'
                         → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
  instr-branch-listcons  : ∀ {τ l Γ₁}
                         → (idx : (listcons τ) ∈ Γ)
                         → Π [ l ]= Γ₁ → (idx ∷= nil) ⊂ Γ₁
                         → Π ⊢ Γ ⇒ Γ
  instr-branch-nil       : ∀ {Γ₁ l} → x ∈ Γ
                         → Π [ l ]= Γ₁ → Γ ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
  instr-fetch-0-new      : ∀ {τ} → listcons τ ∈ Γ
                         → Π ⊢ Γ ⇒ (τ ∷ Γ)
  instr-fetch-0-upd      : ∀ {τ τ'} → listcons τ ∈ Γ
                         → (idx : τ' ∈ Γ)
                         → Π ⊢ Γ ⇒ (idx ∷= τ)
  instr-fetch-1-new      : ∀ {τ} → (listcons τ) ∈ Γ
                         → Π ⊢ Γ ⇒ (list τ ∷ Γ)
  instr-fetch-1-upd      : ∀ {τ τ'} → (listcons τ) ∈ Γ
                         → (idx : τ' ∈ Γ)
                         → Π ⊢ Γ ⇒ (idx ∷= list τ)
  instr-cons-new         : ∀ {τ τ₀ τ₁} → τ₀ ∈ Γ
                         → τ₁ ∈ Γ → list τ₀ ⊔ τ₁ ~ list τ
                         → Π ⊢ Γ ⇒ (listcons τ) ∷ Γ
  instr-cons-upd         : ∀ {τ τ₀ τ₁ τ₂} → τ₀ ∈ Γ
                         → τ₁ ∈ Γ → (idx : τ₂ ∈ Γ)
                         → list τ₀ ⊔ τ₁ ~ list τ
                         → Π ⊢ Γ ⇒ (idx ∷= listcons τ)
\end{spec}

%format _∈_ = "\D{\_\hspace{-2pt}\in\hspace{-2pt}\_}"
%format _∷=_ = "\F{\_\hspace{-2pt}::=\hspace{-2pt}\_}"

In our approach, all name binding is done with statically checked \emph{de Bruijn}
indices~\cite{DEBRUIJN72}, a technique for handling binding by using a nameless,
position-dependent naming scheme. For example, we use a well-typed \emph{de Bruijn}
index |τ ∈ Γ|, which witnesses the existence of an element |τ| in |Γ|,
as defined by the standard library |_∈_| operator. This technique is well-known for
avoiding out-of-bound errors.

\paragraph{Sequencing instructions}{The constructor |instr-seq| is used to
express a sequence of instructions. From the execution of two instructions, it
produces a modified typing context containing the changes performed by
both instructions.}

\paragraph{Conditional jump}{There are three constructors (|instr-branch-list|,
|instr-branch-listcons|, and |instr-branch-nil|) for expressing a conditional
jump. They are used to perform a jump to a label |l| when the received variable is |nil|.
All these constructors type-check the typing context of the intended label with the
current typing context. We use |Π [ l ]= Γ₁|, meaning that there exist a typing context
|Γ₁| in program typing |Π| related to label |l|. And we use |Γ ⊂ Γ₁| as a proof of
subtyping between |Γ| and |Γ₁|. The operator |_∷=_| is used to update the context |Γ|
in the position defined by the index |idx|.}

\paragraph{Fetching information from list}{There are four constructors for expressing
information fetching from a given list. The constructor |instr-fetch-0-new| receives a
non-empty list (of type |listcons τ|), and is used to retrieve the head of this list and store it
in a fresh new variable. The resulting typing context adds the information about the new
variable. Constructor |instr-fetch-0-upd| is also used to retrieve the head element of a
list, however storing its value in an existing variable, represented by the \emph{de Bruijn}
index |idx : τ' ∈ Γ|. The constructors |instr-fetch-1-new| and |instr-fetch-1-upd|
are similar, but fetching the tail of a list instead of the head.}

%format _⊔_~_ = "\D{\_\sqcup\_=\_}"

\paragraph{List construction}{The |instr-cons-new| and |instr-cons-upd| constructors are
used to create a new list. The first creates a new variable, and the second updates an
existing variable. The list is created from two variables, |τ₀ ∈ Γ| and |τ₁ ∈ Γ|,
which are represented as \emph{de Bruijn} indices. The type of the new list is defined by
the least common supertype\footnote{A complete explanation about the least common supertype
can be found in the original list-machine paper~\cite{Appel07}.}, which is defined by the
type |τ₁ ⊔ τ₂ ~ τ|, which encodes that the least common supertype of |τ₁| and |τ₂| is |τ|.
The resulting typing context adds information about the newly created list.
Subsection~\ref{sec:supertype} provides the details of an algorithm
for calculating the least common supertype of two given types.}

%\footnote{The code of this definition is omitted here, but can be found
%in our online repository.}

%format block-halt = "\Con{block\textrm{-}halt}"
%format block-seq = "\Con{block\textrm{-}seq}"
%format block-jump = "\Con{block\textrm{-}jump}"

The representation of blocks is defined as follows.

\begin{spec}
data Block (Π : PCtx) (Γ : Ctx) : Ctx →  Set where
  block-halt  : Block Π Γ Γ
  block-seq   : ∀ {Γ' Γ''} → Π ⊢ Γ ⇒ Γ'
              → Block Π Γ' Γ'' → Block Π Γ Γ''
  block-jump  : ∀ {l Γ₁ Γ'} → Π [ l ]= Γ₁
              → Γ ⊂ Γ₁ → Block Π Γ Γ'
\end{spec}

Constructor |block-halt| can be used to stop the execution of a given block, |block-seq| has a
similar meaning to instruction sequence, and |block-jump| is used to perform a direct jump
(without any condition), receiving a label and checking if the current context typing is a
subtype of the intended one.

%format λ = "\lambda"
%format Program = "\D{Program}"
%format All = "\D{All}"

And finally, a |Program| is a sequence of instruction blocks, each preceded by a label.
We use the |All| datatype to express this relation.

\begin{spec}
Program : PCtx → Set
Program Π = ∀ {Γ'} → All (λ Γ → Block Π Γ Γ') Π
\end{spec}

\subsection{Subtyping and least common supertype}\label{sec:supertype}

%format lub-0 = "\Con{lub0}"
%format lub-1 = "\Con{lub1}"
%format lub-4 = "\Con{lub4}"
%format lub-2 = "\Con{lub2}"
%format lub-2b = "\Con{lub2b}"
%format lub-3 = "\Con{lub3}"
%format lub-5 = "\Con{lub5}"
%format lub-6 = "\Con{lub6}"
%format lub-7 = "\Con{lub7}"
%format lub-comm = "\F{\sqcup\textrm{-}comm}"
%format lub-subtype = "\F{\sqcup\textrm{-}subtype}"
%format lub-least = "\F{\sqcup\textrm{-}least}"
%format <: = "\D{<:}"

A key feature of the list-machine type system is its subtyping (denoted by |<:|), which is
exposed by the least common supertype relation. We omit the Agda encoding of the subtyping relation for
brevity, since it is just an inductive type that encodes the rules presented
in Section~\ref{sec:list}. Several lemmas about subtyping, including its decidable test,
are defined in our source-code repository~\cite{list-rep}.

The least common supertype relation is used by the list-machine type system to refine a
variable type whenever it is updated by a \emph{cons} instruction. The rules of the
supertype relation are specified as the following inductive type:

\begin{spec}
data _⊔_~_ where
  lub-0 : ∀ {t} → t ⊔ t ~ t
  lub-1 : ∀ {t} → (list t) ⊔ nil ~ (list t)
  lub-4 : ∀ {t} → nil ⊔ (list t) ~ (list t)
  lub-2 : ∀ {t t1 t'} → (list t) ⊔ (list t1) ~ t' →
          (list t) ⊔ (listcons t1) ~ t'
  lub-2b : ∀ {t t1 t'} → (list t) ⊔ (list t1) ~ t' →
           (listcons t) ⊔ (list t1) ~ t'
  lub-3 : ∀ {t t1 t'} → t ⊔ t1 ~ t' →
            (list t) ⊔ (list t1) ~ (list t')
  lub-5 : ∀ {t} → (listcons t) ⊔ nil ~ (list t)
  lub-6 : ∀ {t} → nil ⊔ (listcons t) ~ (list t)
  lub-7 : ∀ {t t1 t'} → t ⊔ t1 ~ t' →
            (listcons t) ⊔ (listcons t1) ~ (listcons t')
\end{spec}
The presented constructors ensure that the relation is compatible with \emph{list} and \emph{listcons}
types. Also, we have a rule to ensure that the relation is commutative, as proved by a simple
Agda theorem.
\begin{spec}
lub-comm : t1 ⊔ t2 ~ t3 → t2 ⊔ t1 ~ t3
\end{spec}
We omit the complete definition of |lub-comm| for brevity. In the list-machine benchmark definition,
Appel et. al.~\cite{AppelDL12} also define that the least common supertype relation is sound and complete with respect to the
subtyping relation. Again, we omit the definitions of these properties, however their types are presented below.
%format × = "\D{\land}"
\begin{spec}
lub-subtype : t1 ⊔ t2 ~ t3 → (t1 <: t3) × (t2 <: t3)
lub-least : t1 ⊔ t2 ~ t3 → t1 <: t3 → t2 <: t3 → t3 <: t4
\end{spec}
%format lub = "\F{lub}"
An algorithm to construct the least supertype from two input types is
defined by function |lub|. Note that the |lub|'s type ensures that the
returned type |t| is indeed the least common supertype of |t1| and |t2|,
thus ensuring its correctness-by-construction.

\begin{spec}
lub : (t1 t2 : Ty) → ∃ (λ t → t1 ⊔ t2 ~ t)
lub nil nil = nil , lub-0
lub (list t1) nil = list t1 , lub-1
lub (list t1) (list t2) with lub t1 t2
...| t3 , p = list t3 , lub-3 p
lub (listcons t1) nil = list t1 , lub-5
lub (listcons t1) (list t2) with lub t1 t2
...| t3 , p = list t3 , lub-2b (lub-3 p)
lub (listcons t1) (listcons t2) with lub t1 t2
...| t3 , p = listcons t3 , lub-7 p
-- some code omitted for brevity
\end{spec}

\section{A definitional interpreter}\label{sec:semantics}

This section describes the steps to evaluate a program written using the list-machine language.
We adapted the small-step semantics presented in Section~\ref{sec:list}, transforming it into a
definitional interpreter~\cite{Reynolds72}, which evaluates an intrinsically-typed instruction,
transforming an initial memory state into a new one, represented by a run-time environment.

%format Val = "\D{Val}"
%format []v = "\Con{[]v}"
%format _∷_ = "\Con{\_::\_}"
%format _∷v_ = "\Con{\_::v\_}"

\paragraph{Values and environments}{The interpreter presented next needs to encode a run-time
environment to hold values associated to variables and their types. This way, we define the
notion of a well-typed value as follows.}

\pagebreak

\begin{spec}
data Val : Ty → Set where
  nil : Val nil
  []v : ∀ {t} → Val (list t)
  _∷_ : ∀ {t} → Val t → Val (list t) → Val (listcons t)
  _∷v_ :  ∀ {t} → Val t → Val (list t) → Val (list t)
\end{spec}

The datatype |Val| is indexed by a |Ty|, indicating the type associated to each value. The
first two represent |nil| values associated with type |nil| and the empty |list|. The last
two represent non-empty lists, considering the types |listcons| and |list|.

%format Env = "\D{Env}"
%format PEnv = "\D{PEnv}"
%format Allv = "\D{Allv}"

We use the datatype |All| (and |Allv| for vectors) to define the notion of well-typed
variable environments and well-typed programs. Thus, intuitively, |Env| is like a
list of well-typed values. And |PEnv| is like a list of well-typed environments.
Both typing contexts are used to type block instructions and sequences of
block instructions.

\begin{spec}
Env : Ctx → Set
Env Γ = All Val Γ
\end{spec}

\begin{spec}
PEnv : PCtx → Set
PEnv Π = Allv Env Π
\end{spec}

%format run-step = "\F{run\textrm{-}step}"
%format []=⇒lookup = "\F{[]\textrm{=}{\Rightarrow}lookup}"
%format ⊂-Ctx = "\F{\subset\hspace{-3pt}\textrm{-}Ctx}"
%format update-env = "\F{update\textrm{-}env}"
%format lookupA = "\F{lookupA}"
%format <:-val = "\F{<:\textrm{-}val}"
%format list-<:-inv = "\F{list\textrm{-}<:\textrm{-}inv}"
%format lub-subtype-left = "\F{lub\textrm{-}subtype\textrm{-}left}"
%format lub-subtype-right = "\F{lub\textrm{-}subtype\textrm{-}right}"
%format lub-of-subtype = "\F{lub\textrm{-}of\textrm{-}subtype}"

%format Fuel = "\D{Fuel}"
%format Program = "\D{Program}"
%format Maybe = "\D{Maybe}"
%format sym = "\D{sym}"

%format nothing = "\Con{nothing}"
%format just = "\Con{just}"
%format suc = "\Con{suc}"
%format ∷v = "\Con{::\hspace{-2pt}v}"

%format rewrite = "\mathkw{rewrite}"

\paragraph{Fuel based evaluation}{Having all the building blocks to make the
complete interpreter for the list-machine language, we can start the definition of
the |run-step| function. It is important to note that Agda is a total language,
i.e., each program developed in it must terminate and all possible patterns must
be matched. However, by using the mechanisms for jumping between labels, one could
write a program which never ends, making it impossible to implement a terminating
interpreting function. Following the common practice, we define a fuel based
evaluator~\cite{Amin17,Owens2016}. Basically, what we do is to parameterize the
interpreter over a step index of \emph{fuel value} (represented as a natural
number $n$), which bounds the amount of work the interpreter is allowed to do,
and is decremented on each recursive call.}

The evaluation function is defined with the following type.

\begin{spec}
run-step  : ∀ {Π Γ Γ'} → Fuel → Program Π → Env Γ
          → Block Π Γ Γ' → Maybe (Env Γ')
\end{spec}

The function |run-step| receives four arguments and returns a |Maybe| value. The
first argument is the \emph{fuel}, used to ensure the evaluator always terminates.
The second parameter is a |Program Π|, which contains information about all the
program blocks. The third parameter is the run-time variable environment. And the
last one is the |Block| to be evaluated. This function returns a modified run-time
environment (|Env Γ'|) in case of success, or |nothing| when (and only) the \emph{fuel} runs out.

From now on we describe how we implement some parts\footnote{The complete evaluation
function can be found in our online repository~\cite{list-rep}.} of the dynamic semantics (reduction rules)
of the list-machine language in the function |run-step|. We mix the code with the explanation
to make it easier for the reader.

\paragraph{Out of fuel}{The interpreter stops abruptly when the \emph{fuel} counter
reaches |zero|, and the |run-step| function returns |nothing|. This definition makes our
evaluation function structurally recursive on the \emph{fuel} argument. }

\begin{spec}
run-step zero p env b = nothing
\end{spec}

All the next pieces of code match the value |suc fuel| for the first argument of |run-step|,
meaning that there is still \emph{fuel} during the recursive processing of this function.

%run-step (suc n) p env block-halt = just env
%run-step (suc n) p env (block-seq (instr-seq i₁ i₂) b) =
%  run-step n p env (block-seq i₁ (block-seq i₂ b))
%run-step {Π} (suc n) p env (block-seq (instr-branch-list {τ} {i} v l s) b)
%  with lookup env v
%... | []v rewrite sym ([]=⇒lookup l) =
%  run-step n p (⊂-Ctx s (update-env env v nil)) (lookupA i p)
%... | v₁ ∷v v₂ = run-step n p (update-env env v (v₁ ∷ v₂)) b
%run-step (suc n) p env (block-seq (instr-branch-listcons v l s) b) =
% run-step n p env b

\paragraph{Conditional jump}{We show next only the case when the jump actually occurs,
following the rule \emph{step-branch-taken} of \cite{Appel07}. In this case, variable |v|
has value |nil|, and
the step of evaluation should proceed with the block instruction defined in program |p|, with
environment |env| respecting the subtyping constraint. We use the function |lookupA| to obtain
the block instruction with index |i| on program |p|. Since we use \emph{de Bruijn} indices to
represent the label, only valid values are accepted by the intrinsically-typed syntax. We use
Agda's standard library function |[]=⇒lookup|:

\vspace{-1ex}

\begin{spec}
[]=⇒lookup : ∀ {px : P x} {pxs : All P xs} {i : x ∈ xs} →
             pxs [ i ]= px →
             lookupA pxs i == px
\end{spec}

\vspace{-1ex}

which rewrites a lookup predicate (|pxs [ i ]= px|) into an equality using the |lookupA|
function, |lookupA pxs i == px|.}

\vspace{-1ex}

\begin{spec}
run-step (suc n) p env (block-seq (instr-branch-nil {l = i} v l s) b)
  rewrite sym ([]=⇒lookup l)
    = run-step n p (⊂-Ctx s env) (lookupA i p)
\end{spec}

\vspace{-1ex}

%format lookup = "\F{lookup}"

\paragraph{Fetching list information}{The next code shows the evaluation of two syntactical constructors,
both related to the \emph{step-fetch-field-0} rule~\cite{Appel07}. The first retrieves the head element of a list, and
stores it in a new variable. The |lookup| function projects the value of variable |v| from the run-time
environment |env|, and this variable is added to the result environment. The typed \emph{de Bruijn}
indices guarantee that the projected value has the type demanded, since the environment |env| is typed
by the context |Γ|. Similarly, the second instruction also retrieves the head element of a list, however
it needs to update the run-time environment on the position of index |v'|. This process is done by the
function |update-env|\footnote{The source-code of this function can be found in our online
repository~\cite{list-rep}.}.}

\vspace{-1ex}

\begin{spec}
run-step (suc n) p env (block-seq (instr-fetch-0-new v) b)
  with lookup env v
...| v₁ ∷ v₂ = run-step n p (v₁ ∷ env) b
run-step (suc n) p env (block-seq (instr-fetch-0-upd v v') b)
  with lookup env v
...| v₁ ∷ v₂ = run-step n p (update-env env v' v₁) b
\end{spec}

\vspace{-1ex}

%run-step (suc n) p env (block-seq (instr-fetch-1-new v) b)
%  with lookup env v
%...| v₁ ∷ v₂ = run-step n p (v₂ ∷ env) b
%run-step (suc n) p env (block-seq (instr-fetch-1-upd v v') b)
%  with lookup env v
%...| v₁ ∷ v₂ = run-step n p (update-env env v' v₂) b

\paragraph{List creation}{To evaluate the instruction which creates a new list and respect the expected
types, we need some extra lemmas. First because when we create a list from variables |v₀| and |v₁|, the
result type of this list is the least common supertype between these two. As before, we use the |lookup|
function to retrieve the type information using the \emph{de Bruijn} indices of both variables, and we
extend the run-time environment |env| with the type of the created list. To convince the Agda's
type-checker the new environment is well-typed we use subtyping lemmas, such as |<:-val| and |list-<:-inv|,
and others lemmas to deal with the least common supertype, such as |lub-subtype-left|, |lub-subtype-right|,
and |lub-of-subtype|. These lemmas and their proofs can be found in our repository online~\cite{list-rep}. }

\begin{spec}
run-step (suc n) p env (block-seq (instr-cons-new v₀ v₁ s) b)
  = run-step n p ((<:-val (list-<:-inv (lub-subtype-left
    (lub-of-subtype (lub-subtype-left s)))) (lookup env v₀)
    ∷ <:-val (lub-subtype-right s) (lookup env v₁)) ∷ env) b
\end{spec}

It is worth noticing that we do not have any error treatment on this interpreter function, except for
when we ran out-of-fuel. Since we are using an intrinsically-typed syntax, only valid (well-typed) instructions
are accepted in each step of evaluation.

%run-step (suc n) p env (block-seq (instr-cons-upd v₀ v₁ v' s) b)
%  = run-step n p (update-env env v' (<:-val (list-<:-inv
%    (lub-subtype-left (lub-of-subtype (lub-subtype-left s))))
%    (lookup env v₀) ∷ <:-val (lub-subtype-right s)
%    (lookup env v₁))) b
%run-step (suc n) p env (block-jump {l = i} l s)
%  rewrite sym ([]=⇒lookup l) =
%    run-step n p (⊂-Ctx s env) (lookupA i p)

\paragraph{Soundness properties}{Programs written using an intrinsically-typed syntax are type-sound by
construction. Since only well-typed programs can be expressed, the \emph{preservation} property is
enforced by the host-language type-checker~\cite{Amin17}. By implementing the interpreter in such a
total language like Agda, i.e., specifying the dynamic semantics in a functional way, instead of
relational, we also show the \emph{progress} property, without the need for an extra proof~\cite{Owens2016}.
This approach is promising to be investigated when formalizing even more complex programming languages.}

\section{Type-Checker}\label{sec:typechecker}

In practice, a source-code of a programming language runs through several phases,
including lexing, parsing, scope checking, and most importantly \emph{type-checking}.
Since we represent programs using an intrinsically-typed syntax, scope and
type-checking is only a matter of elaborating an untyped syntax to a typed one.
The definition of our type-checker follows McBride's~\cite{McBride2004} approach which
specifies the type-checker function type as its correctness property: it should return
a type annotated syntax such that it's erasure is equal to the type-checker input program.
%format index = "\F{index}"
%format Lookup = "\D{Lookup}"
%format inside = "\Con{inside}"
%format outside = "\Con{outside}"
%format lookup-var = "\F{lookup\textrm{-}var}"
%format there = "\Con{there}"
%format here = "\Con{here}"
Before considering machine instructions, we will detail the type-checker correctness
approach in the context of variables.
Since we use \emph{de Bruijn} indices to represent labels and variables, as the first
step to type and scope check them, we need to get the index from a given variable.
The function |index| return the list position corresponding to a membership proof (variable):
\begin{spec}
index : ∀ {A : Set}{t : A}{Γ : List A} → t ∈ Γ → ℕ
index (here px) = zero
index (there p) = suc (index p)
\end{spec}
Next, we follow Norell's~\cite{Norell2009} approach and define a type that relates a
natural number with a list as follows. Either the number corresponds to some list position,
in which it is of the form |index p| for some proof |p : x ∈ xs| or it is an invalid position.
The type |Lookup| encodes this relation between lists and natural numbers.
\begin{spec}
data Lookup {A : Set}(xs : List A) : ℕ → Set where
  inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : ∀ {n} → Lookup xs n
\end{spec}
Using this infrastructure we can build the function |lookup-var| which
returns a value of type |Lookup xs n| that specifies whether |n| is
a valid list position or not.

\pagebreak

\begin{spec}
lookup-var : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
lookup-var [] n = outside
lookup-var (x ∷ xs) zero = inside x (here refl)
lookup-var (x ∷ xs) (suc n) with lookup-var xs n
lookup-var (x ∷ xs) (suc .(index p)) | inside y p = inside y (there p)
lookup-var (x ∷ xs) (suc _) | outside = outside
\end{spec}

In order to type-check instructions using this approach, we need to first define a
datatype for untyped programs.

%format map = "\F{map}"
%format ∃ = "\D{\exists}"
%format ≟ = "\D{=}"
%format here = "\Con{here}"
%format there = "\Con{there}"
%format proj₁ = "\D{proj_1}"
%format proj₂ = "\D{proj_2}"
%format yes = "\Con{yes}"
%format no = "\Con{no}"
%format refl = "\Con{refl}"
%format UInstr = "\D{UInstr}"
%format jump = "\Con{jump}"
%format branch-if-nil = "\Con{branch\textrm{-}if\textrm{-}nil}"
%format Label = "\D{Label}"
%format forget-types-instr = "\F{forget\textrm{-}types\textrm{-}instr}"
%format fetch-field-0 = "\Con{fetch\textrm{-}field\textrm{-}0}"
%format fetch-field-1 = "\Con{fetch\textrm{-}field\textrm{-}1}"
%format get-label = "\Con{get\textrm{-}label}"
%format cons = "\Con{cons}"
%format halt = "\Con{halt}"
%format seq = "\Con{seq}"
%format CheckedInstr = "\D{CheckedInstr}"
%format ok = "\Con{ok}"

\begin{spec}
data UInstr (n : ℕ) : Set where
  jump          : (x : ℕ) → Label n → UInstr n
  branch-if-nil : (v : ℕ) → Label n → UInstr n
  fetch-field-0 : (v : ℕ) → (v′ : ℕ) → UInstr n
  fetch-field-1 : (v : ℕ) → (v′ : ℕ) → UInstr n
  get-label     : (v : ℕ) → Label n → UInstr n
  cons          : (v₀ : ℕ) → (v₁ : ℕ) → (v′ : ℕ) → UInstr n
  halt          : UInstr n
  seq           : UInstr n → UInstr n → UInstr n
\end{spec}

Type |UInstr| has a constructor for each of the list machine instructions,
type |Label n| denote a program label and it is represented by
a value of type |Fin n|. Next, we define an erasure function for
our intrinsically typed syntax:

\begin{spec}
forget-types-instr : ∀ {n}{Π : PCtx n}{Γ Γ'} → Π ⊢ Γ ⇒ Γ' → UInstr n
forget-types-instr (instr-seq p p₁) = seq (forget-types-instr p) (forget-types-instr p₁)
forget-types-instr (instr-branch-list {l = l} idx x x₁) = branch-if-nil (index idx) l
forget-types-instr (instr-branch-listcons {l = l} idx x x₁) = branch-if-nil (index idx) l
forget-types-instr (instr-branch-nil {l = l} x x₁ x₂) = branch-if-nil (index x) l
forget-types-instr (instr-fetch-0-new {v' = v'} x) = fetch-field-0 (index x) v'
forget-types-instr (instr-fetch-0-upd x idx) = fetch-field-0 (index x) (index idx)
forget-types-instr (instr-fetch-1-new {v' = v'} x) = fetch-field-1 (index x) v'
forget-types-instr (instr-fetch-1-upd x idx) = fetch-field-1 (index x) (index idx)
forget-types-instr (instr-cons-new {v' = v'} x x₁ x₂) = cons (index x) (index x₁) v'
forget-types-instr (instr-cons-upd x x₁ idx x₂) = cons (index x) (index x₁) (index idx)
\end{spec}

Finally, we can define a view of an untyped instruction (|UInstr n|) as being the
erasure of an intrinsically-typed one using the type |CheckedInstr|:
\begin{spec}
data CheckedInstr {n}(Π : PCtx n) (Γ : Ctx) : UInstr n → Set where
  ok : ∀ {Γ'} → (i : Π ⊢ Γ ⇒ Γ') → CheckedInstr Π Γ (forget-types-instr i)
\end{spec}

%format check-fetch-field-0 = "\F{check\textrm{-}fetch\textrm{-}field\textrm{-}0}"
%format type-error = "\Con{type\textrm{-}error}"
%format TC = "\D{TC}"
%format CheckedInstr = "\D{CheckedInstr}"

%format fetch-field-0 = "\Con{fetch\textrm{-}field\textrm{-}0}"
%format right = "\Con{right}"
%format ok = "\Con{ok}"
%format undefined-var = "\Con{undefined\textrm{-}var}"
%format TypeError = "\D{TypeError}"
%format UnexpectedTy = "\Con{UnexpectedTy}"
%format UndefinedVar = "\Con{UndefinedVar}"
%format UndefinedLabel = "\Con{UndefinedLabel}"
%format ContextSubtyping = "\Con{ContextSubtyping}"
%format Either = "\D{Either}"
%format left = "\Con{left}"
%format right = "\Con{right}"
For brevity, we show how we type-check only one instruction\footnote{The curious reader can refer to our
online repository~\cite{list-rep} for a complete implementation.}. Function |check-fetch-field-0|
receives a program context, a typing context, and two named variables, and returns a |TC| value:
\begin{spec}
TC : Set → Set
TC i = Either TypeError i
\end{spec}
which is either an error message or a |CheckedInstr| indicating that the term type-checks.
The |TypeError| contains one constructor for each of the possible failures causes for an
input program.
\begin{spec}
data TypeError : Set where
  UnexpectedTy : Ty → TypeError
  UndefinedVar : ℕ  → TypeError
  UndefinedLabel : ∀ {n} → Label n → TypeError
\end{spec}
In the code below, we use the function |lookup-var| to provide the \emph{de Bruijn} indices for
each variable, and match the first with its possible forms. The first three cases indicate
type errors: (1) when |v| is |outside| it means a variable scope error; (2) and (3) are typing errors,
since the type of variable |v| should be a |listcons|. Last two cases represent that the instruction
is well-typed. The process for type-checking different instructions follows a similar setting.

\pagebreak

\begin{spec}
check-fetch-field-0 : ∀ {n}(Π : PCtx n) Γ v v' 
                    → TC (CheckedInstr Π Γ (fetch-field-0 v v'))
check-fetch-field-0 Π Γ v v' with lookup-var Γ v | lookup-var Γ v'
... | outside | _ = undefined-var v
... | inside nil p | q = type-error nil
... | inside (list x) p | q = type-error (list x)
... | inside (listcons x) p | inside x₁ p₁ = right (ok (instr-fetch-0-upd p p₁))
... | inside (listcons x) p | outside = right (ok (instr-fetch-0-new p))
\end{spec}
Finally, functions |type-error| and |undefined-var| just build the corresponding
type-checker error as follows:
\begin{spec}
type-error : ∀ {i} → Ty → TC i
type-error = left ∘ UnexpectedTy

undefined-var : ∀ {i} → ℕ → TC i
undefined-var = left ∘ UndefinedVar
\end{spec}

\section{Extending the List-Machine with Indirect Jumps}\label{sec:indirect}

In this section we describe the necessary modifications to our formalization to include indirect jumps
as proposed by Appel et. al.~\cite{AppelDL12}. We start by describing the changes on the type system
and its impact on the intrinsically typed representation of programs in Section~\ref{sec:changestypes}.
Updates on the type checker and the interpreter implementations are described in Sections~\ref{sec:changestypechecker}
and ~\ref{sec:changesintep}, respectively.

\subsection{Modifications in the type system and instruction set}\label{sec:changestypes}

Since our solution relies on representing the program using intrinsically typed syntax, we first
describe the changes on the list-machine type system. The first modification is the inclusion of a type for
program labels, which denotes continuations in a program.

%format top = "\Con{\top}"
%format bot = "\Con{\bot}"
%format cont = "\Con{cont}"

\pagebreak

\begin{spec}
data Ty : Set where
  nil top bot : Ty
  list listcons : Ty → Ty
  cont : Ctx → Ty
\end{spec}

The type |cont| $\Gamma$ is given to program labels and it
expresses that the machine can safely jump when its registers
satisfies $\Gamma$. The inclusion of continuation types makes
the type and context syntax mutually inductive.

Since we have changed the typed syntax, we need to adapt the definition of the subtyping relation.
The continuation type substantially changes the subtyping relation,
since now we have ``incomparable'' types: list types are not subtypes neither supertypes for continuations.
The solution is to complete the subtyping relation with bottom and top types. The subtyping rules for these
new types are presented next.

\[
\begin{array}{cc}
  \inference{}{\bot <: \tau}[subtype-bot] &
  \inference{}{\tau <: \top}[subtype-top] \\ & \\
  \multicolumn{2}{c}{
    \inference{\Gamma_2 \subset \Gamma_1}{cont\,\Gamma_1\:<:\:cont\,\Gamma_2}[subtype-cont]
  }
\end{array}
\]

We omit their representation in Agda because they are just a direct encoding of these previous rules
in the subtyping relation inductive type. Notice that both subtyping relations for types and
contexts are mutually inductive.

Another major modification in the typing for the list machine is the definition of least upper bounds.
First, we complete the least upper bound relation by specifying that the lub for incomparable types is
$\top$.

\[
\begin{array}{c}
  \inference{}{cont\:\Gamma\:\sqcup\:nil = \top}[lub-cont-nil] \\ \\
  \inference{}{cont\:\Gamma\:\sqcup\:(list\:\tau) = \top}[lub-cont-list]\\ & \\
  \inference{}{cont\:\Gamma\:\sqcup\:(listcons\:\tau) = \top}[lub-cont-listcons]
\end{array}
\]

We omit rules that ensure the commutativity of the least upper bound relation for brevity.
Next, we present the rules for the least upper bound relation for top and bottom types.

\[
\begin{array}{c}
  \inference{}{\tau \sqcup \bot = \tau}[lub-bot] \\ \\
  \inference{}{\tau \sqcup \top = \top}[lub-top]
\end{array}
\]

The last set of rules for the least upper bound relation deals with continuations.
Because of the contravariance of the |cont| type, we also need to define the greatest
lower bound relation for both
types and typing contexts.
First, we present the rule for the least upper bound for continuation types.

\[
\begin{array}{c}
  \inference{\Gamma_1\cap\Gamma_2 = \Gamma_3}
            {cont\:\Gamma_1\:\sqcup\: cont\:\Gamma_2=cont\:\Gamma_3}
            [lub-cont]
\end{array}
\]

The rule specifies that the least upper bound for types |cont| $\Gamma_1$ and |cont| $\Gamma_2$ is
|cont| $\Gamma_3$, where $\Gamma_3$ is the greatest lower bound for typing contexts $\Gamma_1$ and $\Gamma_2$.
The definition of the greatest lower bound for contexts is as follows:
\[
  \begin{array}{c}
    \inference{}{\{\} \cup \Gamma = \Gamma}[glb-empty-left] \\ \\
    \inference{}{\Gamma \cup \{\} = \Gamma}[glb-empty-right] \\ \\
      \inference{\tau_1 \sqcup \tau_2 = \tau_3 & \Gamma_1 \cup \Gamma_2 = \Gamma_3}
                {(\Gamma_1 , x : \tau_1) \cup (\Gamma_2 , x : t_2) = \Gamma_3, x : \tau_3}
                [glb-cons]
  \end{array}
\]
The definition of the greatest lower bound for types is as follows. The first set of rules specify the reflexivity,
that $\top$ type is an identity and $\bot$ is for greatest lower bound for any type $\tau$.
Again, rules to ensure commutativity of the relation are omitted for brevity.

\[
\begin{array}{c}
  \inference{}{\tau \sqcap \tau = \tau}[glb-refl] \\ \\
  \inference{}{\top \sqcap \tau = \tau}[glb-top] \\ \\
  \inference{}{\bot \sqcap \tau = \bot}[glb-bot]
\end{array}
\]
Next, we define the greatest lower bound relation for list types. The first rule specifies that the bottom
type is the greatest lower bound for the empty list type and non-empty list type. Two rules specify the
compatibility of |list| and |listcons| type constructors with the greatest lower bound relation. The last
rule shows that |listcons| $\tau_3$ is the lower bound for |list| $\tau_1$ and |listcons| $\tau_2$.
\[
\begin{array}{c}
  \inference{}{nil \sqcap (listcons\: \tau) = \bot}[glb-nil-listcons] \\ \\
  \inference{\tau_1\sqcap \tau_2 = \tau_3}
            {(list\: \tau_1)\sqcap (list\:\tau_2) = list\:\tau_3}
            [glb-list]\\ \\
   \inference{\tau_1\sqcap \tau_2 = \tau_3}
             {(listcons\: \tau_1)\sqcap (listcons\:\tau_2) = listcons\:\tau_3}
             [glb-listcons] \\ \\

   \inference{\tau_1\sqcap \tau_2 = \tau_3}
             {(list\: \tau_1)\sqcap (listcons\:\tau_2) = listcons\:\tau_3}
             [glb-list-listcons]
\end{array}
\]
Rules for the greatest lower bound relation for continuation types show that the bottom type is the
lower bound for the list and continuation types. The other rule establishes the compatibility of
the continuation type with the lower bound relation and it uses the least upper bound for the typing
context relation.

\[
\begin{array}{c}
  \inference{}{nil\sqcap(cont\:\Gamma) = \bot}[glb-cont-nil] \\ \\
  \inference{}{(list\:\tau)\sqcap(cont\:\Gamma) = \bot}[glb-cont-list] \\ \\
  \inference{}{(listcons\:\tau)\sqcap(cont\:\Gamma) = \bot}[glb-cont-listcons] \\ \\
  \inference{\Gamma_1\cup\Gamma_2 = \Gamma_3}
            {(cont\:\Gamma_1)\sqcap(cont\:\Gamma_2) = (cont\:\Gamma_3)}
            [glb-cont]
\end{array}
\]
We omit several rules for the greatest lower bound relation that ensure the commutativity of the
relation and that $\bot$ type is a lower bound for any type. Rules for the least upper bound for
typing contexts are simply the dual version for greatest lower bound for contexts, as shown next.
\[
  \begin{array}{c}
    \inference{}{\{\} \cap \Gamma = \{\}}[glb-empty-left] \\ \\
    \inference{}{\Gamma \cap \{\} = \{\}}[glb-empty-right] \\ \\
    \inference{\tau_1 \sqcap \tau_2 = \tau_3 & \Gamma_1 \cap \Gamma_2 = \Gamma_3}
              {(\Gamma_1 , x : \tau_1) \cap (\Gamma_2 , x : t_2) = \Gamma_3, x : \tau_3}
              [glb-cons]
  \end{array}
\]
The Agda encoding of these relations is an immediate translation of the mathematical notation.

The modifications on the subtyping and least upper bound induced changes on all theorems
about these relations. On our first implementation, these results are just straightforward
inductive proofs. Because of the mutually inductive nature of the new relation versions, all
these proofs needed to be defined by mutually recursive functions.

Once we have only modified the subtyping and the least upper bound relations, most of the type system
rules remained unchanged from the original version. In order to support indirect jumps, Appel's et. al.
approach is to modify the jump instruction and add a new instruction for loading label values into
machine registers. The typing rules for get-label and jump instructions are as follows.

\[
\begin{array}{c}
  \inference{\Gamma[v\,:=\,nil] = \Gamma'}
            {\Pi\vdash_{instr} \Gamma \{\textrm{get-label}\:v\:L_0\}\Gamma'}
            [check-instr-get-label-0] \\ \\
  \inference{\Pi(l) = \Gamma_1 & \Gamma[v\,:=\,cont\:\Gamma_1] = \Gamma'}
            {\Pi\vdash_{instr} \Gamma \{\textrm{get-label}\:v\:l\}\Gamma'}
            [check-instr-get-label]\\ \\
  \inference{\Gamma(v) = cont\:\Gamma_1 & \Gamma \subset \Gamma_1}
            {\Pi;\Gamma\vdash_{block}\,\textrm{jump}\:v}
            [check-block-jump]
\end{array}
\]
The first rule shows that the type of label $L_0$, the starting label of a complete machine program,
is $nil$ and the second specifies that the type for any other label is a continuation type formed by
the context associated with label $l$ in $\Pi$. The last rule shows that typing a jump instruction
requires that its register has a continuation type, $cont\:\Gamma_1$, that should be a subtype of
the current block context $\Gamma$. Based on these rules, we add the following constructors to our
typed instruction syntax:

%format instr-getlabel-0 = "\Con{instr\textrm{-}getlabel\textrm{-}0}"
%format instr-getlabel = "\Con{instr\textrm{-}getlabel}"

\begin{spec}
data _⊢_⇒_ (Π : PCtx)(Γ : Ctx) : Ctx → Set where
  -- unchanged from the previous code version.
  instr-getlabel-0      : ∀ {τ} → (idx : τ ∈ Γ)
                                → Π ⊢ Γ ⇒ (idx ∷= nil)
  instr-getlabel        : ∀ {l τ Γ₁} → (idx : τ ∈ Γ)
                                     → Π [ l ]= Γ₁
                                     → Π ⊢ Γ ⇒ (idx ∷= cont Γ₁)
\end{spec}
Constructor |instr-getlabel-0| encodes the typing rule for the instruction \textrm{get-label} when
the label involved is the special label $L_0$. Intuitively, the constructor |instr-getlabel-0| type
ensures that the type associated with the register for the instruction is the empty list type.
Next, constructor |instr-getlabel| shows that any other label $l$ should be typed with a continuation
holding the typing context associated with $l$ in $\Pi$.

The needed modifications on the block syntax are presented next.
\begin{spec}
data Block (Π : PCtx) (Γ : Ctx) : Ctx →  Set where
  -- unchanged from the previous code version
  block-jump            : ∀ {l Γ₁} → cont Γ₁ ∈ Γ
                        → Γ ⊂ Γ₁
                        → Block Π Γ Γ₁
\end{spec}
We only need to adapt the type of the constructor for jump by requiring that the register has a
continuation type whose typing context is a subtype of the current block type, which allows
the safe jump to the next block.


\subsection{Modifications in the type-checker}\label{sec:changestypechecker}

Most of the code for the type-checker is unmodified in our new version. We just need to change
the type checking for jumps, which now should validate if a machine register has an appropriate
continuation type.

%format get-label = "\Con{get\textrm{-}label}"
%format L₀ = "\Con{L_{0}}"
%format forget-types-instr = "\F{forget\textrm{-}types\textrm{-}instr}"
%format check-get-label = "\F{check\textrm{-}get\textrm{-}label}"
%format inspect = "\F{inspect}"
%format lookup⇒[]= = "\F{lookup⇒[]=}"
%format with≡ = "\F{with\equiv}"
%format UInstr = "\D{UInstr}"
%format Label = "\D{Label}"
%format lookup = "\F{lookup}"
We also need to include code to check the well-typedness for the get-label instruction. First,
we include a new constructor on type |UInstr| to represent untyped get-label instruction and
add its corresponding equation on function |forget-types-instr|.
\begin{spec}
data UInstr : Set where
  -- same code from before.
  get-label     : (v : ℕ) → Label → UInstr

forget-types-instr : ∀ {Π Γ Γ'} → Π ⊢ Γ ⇒ Γ' → UInstr
-- same code as before...
forget-types-instr (instr-getlabel-0 {x = x} v) = get-label x zero
forget-types-instr (instr-getlabel {l = l} {x = x} v p) = get-label x l
\end{spec}
Constructor |get-label| stores the name for a register and a label which is loaded into the register.
Equations for erasing type information are immediate. The only peculiarity is that when the instruction
|get-label| is typed using rule |instr-getlabel-0| we consider the initial label |zero|.
Next, we implement the type checker logic for |get-label|. Function |check-get-label| verifies if the label is present at
the program global typing context and if the variable is present on the current block typing context.
\begin{spec}
check-get-label : ∀ Π Γ v l  → TC (CheckedInstr Π Γ (get-label v l))
check-get-label Π Γ v l with inspect (lookup Π l)
check-get-label Π Γ v l |  Γ₁ with≡ p with lookup-var Γ v
check-get-label Π Γ .(index p₁) l | Γ₁ with≡ p | inside x p₁
  = right (ok (instr-getlabel p₁ (lookup⇒[]= l Π p)))
check-get-label Π Γ v l | Γ₁ with≡ p | outside = undefined-var v
\end{spec}

\subsection{Modifications in the interpreter}\label{sec:changesintep}

The final piece of our formalization for the version 2.0 of the list-machine benchmark is the modification of
the interpreter implementation. Our first step changed the definition of values to reflect
the changes on the typed syntax, since now we have a new value for continuation types. A continuation
value stores the environment for its corresponding block.

\begin{spec}
  data Val : Ty → Set where
    -- same code as before
    cont : ∀ {Γ₁} → Env Γ₁ → Val (cont Γ₁)
\end{spec}

%format jump = "\Con{jump}"

Since the value definition has changed, we need to modify the lemmas for value and environment
subsumption accordingly. Next, we change the interpreter itself by adding equations for the
|get-label| instruction and adjusting the |jump| implementation.
Equations for |get-label| simply update the current environment using the label. When the
typed syntax is built using constructor |instr-getlabel-0|, the environment is updated with
value |nil|, which denotes the initial continuation for the program execution.
\begin{spec}
run-step (suc n) penv p env (block-seq (instr-getlabel-0 idx) b)
    = run-step n penv p (update-env env idx nil) b
run-step (suc n) penv p env (block-seq (instr-getlabel {l = l} idx x) b)
    = run-step n penv p (update-env env idx (cont x)) b
\end{spec}
The final change in the interpreter is the implementation of the jump instruction. In order to
execute an indirect jump, first we need to get the continuation value associated with its
variable using |lookup env v|. Using the label associated with the retrieved continuation value
we jump to its corresponding block and its entry execution environment.
\begin{spec}
run-step (suc n) penv p env (block-jump v x₁) with lookup env v
  ...| (cont {l = l} k) rewrite sym ([]=⇒lookup k)
    = run-step n penv p (lookupA l penv) (lookupA l p)
\end{spec}

\section{Comparison of Mechanized Proofs}\label{sec:comparison}

We implemented all 14 tasks from the list-machine benchmark in the Agda programming language.
The tasks considered by us are the same implemented and proved by Appel et. al.~\cite{Appel07}.
The next table summarizes the total number of lines of code (LOC) for our results together with theirs.

\begin{table}[!htb]
\begin{tabular}{rl||rrr}
    & Task                                         & \multicolumn{1}{l}{Twelf} & \multicolumn{1}{l}{Coq} & \multicolumn{1}{l}{Agda} \\ \hline
1.  & Operational Semantics                        & 126                       & 98                      & 101                      \\
2.  & Derive $p \Downarrow$                        & 1                         & 8                       & 1                        \\ \hline
3.  & Type System $\vDash_{\textrm{prog}} p : \Pi$ & 167                       & 130                     & 50                       \\
4.  & $\sqcap$ algorithm                           & *                         & *                       & 13                       \\
5.  & Derive $\vDash_{\textrm{prog}} p_{\textrm{sample}} : \Pi_{\textrm{sample}}$
                                                   & 1                         & no                      & 1                        \\
6.  & State properties of $\sqcup$                 & 12                        & 13                      & 6                        \\
7.  & Prove properties of $\sqcup$                 & 114                       & 21                      & 124                      \\
8.  & State soundness theorem                      & 29                        & 15                      & *                        \\
9.  & Prove soundness of $\vDash_{\textrm{prog}} p : \Pi$
                                                   & 2060                      & 315                     & *                        \\ \hline
10. & Efficient algorithm                          & 22                        & 145                     & 98                       \\
11. & Derive $\vdash_{\textrm{prog}} p_{\textrm{sample}} : \Pi_{\textrm{sample}}$
                                                   & 1                         & 1                       & 1                        \\
12. & Prove termination of $\vdash_{\textrm{prog}} p : \Pi$
                                                   & 18                        & 0                       & 0                        \\
13. & Scalable type-checker                        & yes                       & yes                     & yes                      \\
14. & Prove soundness of $\vdash_{\textrm{prog}} p : \Pi$
                                                   & 347                       & 141                     & *                        \\
15. & Generate~\LaTeX                              & no                        & no                      & no
\end{tabular}
\end{table}

The total time for parsing and proof checking our Agda implementation was around 10 seconds
on a machine with a Intel Core I7 1.7 GHz, 8GB RAM running Mac OS X 10.15.5. We briefly comment
on our Agda encoding of these 15 tasks.

\begin{enumerate}
  \item \textbf{Operational semantics.} Instead of using an inductive type for representing the operational semantics, we chose to
        use a definitional interpreter for our intrinsically-typed representation. Our implementation for the operational
        semantics is composed by 38 lines for the typed syntax and 71 for the definitional interpreter.
  \item \textbf{Derive $p \Downarrow$.} Since we used a definitional interpreter for representing the semantics, we can derive
        $p\,\Downarrow$ just by executing the interpreter on $p$.
  \item \textbf{Represent the type system.} Our type system representation consists of the intrinsically-typed encoding of
        the list-machine programs and it is already counted in as part of the operational semantics of our solution.
      \item \textbf{Least common supertype algorithm.} In order to implement this task, we specified the least common super type
        as a relation and implemented the algorithm which shows that this relation is indeed a function. In this way, we
        guarantee its soundness w.r.t. its specification.
  \item \textbf{Derive an example of type-checking.} Our approach to build a derivation for a sample list-machine program
        is just to execute the type-checker over it. Since our type-checker returns an intrinsically-typed representation of
        the input and such typed syntax is equivalent to the type system, it can be used to build type derivations.
  \item \textbf{State properties of the least common supertype.} This is trivial, since it is just a matter to encode the
        desired properties as Agda function types.
  \item \textbf{Prove properties of the least common supertype.} Proofs of all proved properties about the least common supertype
        are simple recursive functions over the least common supertype and subtyping relations definitions and were omitted
        from this text for brevity.
  \item \textbf{State the soundness theorem for the type system.} Following~\cite{Amin17}, we represent the soundness
        theorem statement as the type of our definitional interpreter for the intrinsically-typed syntax for the list-machine
        programs. Therefore, this was done as part of task 9.
  \item \textbf{Prove the soundness theorem for the type system.} Following \cite{Amin17}, the proof of the soundness
        theorem is just the implementation of the definitional interpreter. Soundness is ensured by construction since the interpreter
        produces, as result, an environment of well-typed values resulting from the execution of the input program.
  \item \textbf{Asymptotically efficient algorithm.} Our current implementation of the type-checker takes quadratic time. The reason
        for this inefficiency is the representation of environments as lists / vectors. The use of better data structures (like finite
        maps implemented by efficient search trees) can solve this issue. We leave this fix to future work.
  \item \textbf{Simulate the new algorithm.} This task is just one line of code, since it is only a matter of calling the type-checker
        on the input program.
  \item \textbf{Prove the termination of the type-checker.} This task is trivial in our setting, since all defined Agda functions
        must be total. The totality is ensured by Agda's termination / totality checker.
  \item \textbf{Scalable type-checker.} Agda code can be compiled to machine code using its GHC-Haskell back-end. Since GHC is
        an industrial strength compiler, the back-end can generate an efficient executable for the machine interpreter and type-checker.
  \item \textbf{Prove soundness of type-checker.} In our approach, the soundness of the type-checker is ensured by construction,
        since it returns the intrinsically-typed representation of the input program which corresponds to its typing derivation.
  \item \textbf{Generate~\LaTeX.} Agda's compiler does provide support for typesetting~\LaTeX~code.
        However, we find it lacking some fine-grained formatting features like use~\LaTeX~math-commands instead of
        unicode characters for mathematical symbols.
\end{enumerate}

As we could notice, our approach avoids code repetition and decreases the needed LOCs, when compared to Appel's et. al.
\cite{Appel07} solution.
Our implementation used 415 LOC to complete the tasks, while the Twelf solution demanded 2898 LOC and 887 LOC in Coq.
Our encoding uses approximately 14\% of the LOC when compared to the Twelf formalization, and 47\% when compared to Coq's. The main
reason for this difference is that our intrinsically-typed syntax granted us many properties for free (e.g. type soundness).
%format sub-env = "\F{sub\textrm{-}env}"
Appel et. al. list-machine benchmark 2.0 uses a semantic-based approach to prove type soundness and the
correctness of the type checker~\cite{AppelMRV07}, which rely on a Coq library inspired by modal logics.
However, we are not able to prove a lemma which establishes a coercion between continuation types:

\begin{spec}
postulate sub-env : ∀ {Γ Γ'} → Γ' ⊂ Γ → Env Γ → Env Γ'
\end{spec}

Appel et al. was able to prove this property in Coq by encoding the machine syntax and semantics using
a shallow embedding based on his ``very modal model''~\cite{Appel07}. Using a semantic-based characterization
of typing, like Appel's solution to the list machine benchmark, it has the benefit of allowing a direct proof
of the coercion property for continuation types. While it is certainly possible to construct a modal logic
inspired from their model and from it proving this type coercion result, such approach deviates from our main objective:
to construct a solution to the list machine benchmark using intrinsically-typed syntax and definitional interpreters.
For this reason, we decided to postulate this coercion property and stick with our original proposal.
Our formalization demanded 1134 LOC and it depends only on the Agda standard library, while Appel et. al.
solution demanded around 1750 LOC without considering his ``very modal model'' library.
Compared to our solution to the first version of the benchmark (which was implemented in 612 LOC),
the inclusion of indirect jumps increased the formalization size by around 85\%.

\section{Related work}\label{sec:related}

\paragraph{Benchmarks for PL mechanization}{
The importance of benchmarks is recognized in several areas in computer science. A relevant example is the
TPTP library for the theorem proving community~\cite{Sut17}. In the context of the programming languages community,
we have the POPLMark challenge~\cite{Aydemir05}, which was developed by a renowned group of programming language researchers aiming
at the collaboration between the PL community and the proof assistants researchers. The main objective of this challenge
was to motivate authors to formalize all of their theorems using such tools. Since the focus of the POPLMark challenge
was mainly the formalization of type soundness theorems, other benchmarks were proposed with different objectives. The list
machine benchmark was proposed by Appel and Leroy~\cite{Appel07} as an exercise in formalizing results that interest
compiler oriented research and also provides Twelf and Coq solutions to this benchmark. Our work provides another
solution to this benchmark using an intrinsically-typed approach in the Agda programming language. Representation of binding syntax
was the subject of~\cite{FeltyMP18} which proposed a set of problems and research questions for tools
that use the high-order abstract syntax approach for name binding. Since the list-machine benchmark definition avoids
name binding issues because they are orthogonal to most of compiler related proofs~\cite{Appel07}, we just ensure
the correct manipulation of names by following the traditional \emph{de Bruijn} approach. Finally, a recent problem set
was proposed by~\cite{Pientka18}, named POPLMark challenge reloaded, focusing on the mechanization
of logical relation arguments, like strong normalization theorems.}

\paragraph{Definitional interpreters and intrinsically-typed syntax}{
The use of definitional interpreters for specifying semantics dates back to Reynold's pioneer work~\cite{Reynolds72}.
Recently, the interest on such interpreters was revitalized by~\cite{Amin17}, which used definitional
interpreters, implemented in Coq, to prove type soundness theorems for non-trivial typed languages like System F$_{<:}$.
Unlike our work, Amin and Rompf's formalizations do not use intrinsically-typed representations of their syntax, what cluttered
their formalization with the need of dealing with ``stuck states'' in the semantics. \cite{Poulsen18} described how
definitional interpreters for imperative languages can be much concisely implemented by using intrinsically-typed syntax and a
library for name binding using \emph{scope graphs}, which greatly simplifies the treatment of complex
binding structures. Since the list-machine benchmark was designed to address other problems than binding, our representation
using \emph{de Bruijn} indices was sufficient to implement the desired type-checker and interpreter.
Other recent application of definitional interpreters was proposed by~\cite{Rouvoet20}. The main contribution
of Rouvoet et. al. was to define interpreters for linear typed languages supporting session based concurrency. In order to model
linear typing features in the interpreter, the authors have implemented monads based on a separation algebra which they
named \emph{Market}, supporting the main operations for accessing and updating the store used by the interpreter.
Another work using intrinsically-typed syntax for resource control was developed by~\cite{Thiemann19}, which
implemented an interpreter for a more realistic core functional session typed calculus including recursion and
session subtyping in Agda. Thiemann modeled the semantics as an interruptible abstract machine which provides a
simple interface to a scheduler. Since our objective was to formalize the list-machine benchmark in Agda and it
does not have linearity constraints in its state manipulation, we do not need to deal with the complexities
of linear and session types as in~\cite{Rouvoet20,Thiemann19}. A formalization of System F$_{\omega\mu}$ was
the subject of \cite{ChapmanKNW19} work, which used an intrinsically-typed representation to
implement a normalization by evaluation for this calculus. The reason behind such formalization effort was
the verification of a core language for smart-contracts which is based on System F$_{\omega\mu}$. As our work,
Chapman's et al. formalization is an example of how intrinsically-typed syntax leads to clear interpreter code
which avoids completely stuck states. Another application of intrinsically-typed syntax is Pardo's et. al. work on correct-by-construction
compilers~\cite{PardoGPV18}. The approach used by the authors is to index the syntax of
a language with its types and semantics in order to automatically derive a correctness proof for the
compiler. Authors apply their methodology in an arithmetic expression languages and a imperative
language with top-level variables, sequencing and looping statements. }

\vspace{-3ex}

\section{Conclusion}\label{sec:conclusion}

This paper shows how the combination of intrinsically-typed syntax and definitional interpreters can be used to simplify
the tasks on the formalization of programming languages. Using such approach, we were able to provide a machine-checked
version of the two versions of the list-machine benchmark in Agda, showing that the approach is useful to
formalize both high-level and low-level languages.
The ideas presented here can be exploited on the formalization of real-world virtual machines, such as the JVM and LUA VM,
since we were able to encode features such as jumps, mutable state, and sub-typing. When comparing our work with the
conventional non-dependently typed formalization strategies (like the one used in~\cite{Appel07} in their Coq and Twelf implementations),
we can affirm that it requires a fewer number of lines to achieve the same result, even without the use of proof automation.
This happens because the approach uses the power of the host language, and provides some proofs for free due to the
intrinsically-typed syntax.

As future work, we want to reuse the ideas presented in this paper to provide an intrinsically-typed formalization for
real-world low-level languages like the eBPF and the LUA VM. Furthermore, one can extend the formalization presented here
for other programming languages with similar settings.

\bibliography{main}

\end{document}
