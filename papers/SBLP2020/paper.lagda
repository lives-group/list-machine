\documentclass[sigconf]{acmart}

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
%if False
\begin{code}
module paper where
\end{code}
%endif

% Copyright
%\setcopyright{none}
%\setcopyright{acmcopyright}
\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\setcopyright{usgov}
%\setcopyright{usgovmixed}
%\setcopyright{cagov}
%\setcopyright{cagovmixed}

\AtBeginDocument{%
  \providecommand\BibTeX{{%
    \normalfont B\kern-0.5em{\scshape i\kern-0.25em b}\kern-0.8em\TeX}}}

\setcopyright{acmcopyright}
\copyrightyear{2020}
\acmYear{2020}


\acmConference[SBLP '20]{SBLP '20: Brazilian Symposium on Programming Languages}{October 19--23, 2020}{Natal, Brazil}
\acmBooktitle{SBLP '20: Brazilian Symposium on Programming Languages,
  October 19--23, 2020, Natal, Brazil}

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

\begin{document}


%%%%%%%%%%%%%%%%%%%%%%%
%% Title and authors %%
%%%%%%%%%%%%%%%%%%%%%%%



\title{A Certified Interpreter for the List Machine Benchmark}

\author{Samuel Feitosa}
\authornotemark[1]
\email{samuel.feitosa@@ifsc.edu.br}
\affiliation{%
  \institution{Departamento de Informática}
  \streetaddress{Instituto Federal de Santa Catarina}
  \city{Caçador}
  \state{Santa Catarina}
  \country{Brazil}
}

\author{Rodrigo Ribeiro}
\email{rodrigo.ribeiro@@ufop.edu.br}
\affiliation{%
  \institution{Prog. Pós Graduação em Ciência da Computação}
  \streetaddress{Universidade Federal de Ouro Preto}
  \city{Ouro Preto}
  \state{Minas Gerais}
  \country{Brazil}}


%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract          %%
%%%%%%%%%%%%%%%%%%%%%%%



\begin{abstract}
Formal models are important tools in the programming languages research
community. However, such models are full of intricacies and, due to that,
they are subject to subtle errors. Such failures motivated the usage of
tools to ensure the correctness of these formalisms. One way to eliminate
such errors is to encode models in a dependently-typed language in order
to ensure its ``correctness-by-construction''.

In this work, we use this idea to build a verified interpreter
for the list machine benchmark in the Agda programming language.
\end{abstract}


%%%%%%%%%%%%%%%%%%%%%%%%%
%% ACM codes for areas %%
%%%%%%%%%%%%%%%%%%%%%%%%%



\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011039.10011311</concept_id>
<concept_desc>Software and its engineering~Semantics</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10011007.10011006.10011041.10010943</concept_id>
<concept_desc>Software and its engineering~Interpreters</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003752.10003790.10011740</concept_id>
<concept_desc>Theory of computation~Type theory</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Semantics}
\ccsdesc[500]{Software and its engineering~Interpreters}
\ccsdesc[500]{Theory of computation~Type theory}

\keywords{Dependent types, formal semantics}

\maketitle

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

The development of a new programming language design, linguistic construct
or type system involves its careful formalization in order to express
its core ideas in a concise way. However, such models have many details
and complexities which can hinders its correctness assurances.
Because of such problems, the programming languages research community
started to use tools, like proof assistants~\cite{Stump16,Chlipala13},
and benchmark problems to validate them and stress its suitability for
such specification tasks~\cite{Aydemir05,Pientka18,Appel07}.

A popular approach for specifying formal semantics is the
use of definitional interpreters, which represents the meaning of a
programming language as an interpreter written in some
meta-language~\cite{Reynolds72}. A major advantage of such approach
is the possibility of validating the semantics through execution.
Recently, definitional interpreters were used to formalize type
soundness theorems for some advanced typing features~\cite{Amin17}
and the semantics of imperative programming languages in which static
semantics is ensured by dependently-typed
syntax\footnote{Also known as intrinsically-typed.}~\cite{Poulsen18}.
In this work, we follow Poulsen et. al and use an intrinsically-typed
representation to build a definitional interpreter for a low-level virtual
machine developed by Appel and Leroy as a benchmark problem closer to
real-world implementations like typed assembly languages~\cite{CraryM99} and
proof carrying code~\cite{Necula97}.

More specifically, we contribute:

\begin{itemize}
  \item We show how all the details of the list machine type system
        can be encoded as dependently-typed syntax which avoids, by construction,
        the presence of stuck states in its definitional interpreter.
  \item We provide a provably correct implementations for testing the subtyping
        relation and to calculate the least common super type of two input
        types for the machine registers.
\end{itemize}

The rest of this paper is organized as follows. Section~\ref{sec:agda}
presents a brief introduction to Agda and Section~\ref{sec:list}
reviews the list machine benchmark and presents its syntax and type system.
We describe the intrinsically-typed representation for the list machine syntax,
the subtyping relation and the least common super type algorithm in
Section~\ref{sec:typing}. The list machine semantics and its realization as
a definitional interpreter are presented in Section~\ref{sec:semantics}.
Related work is discussed in Section~\ref{sec:related},
and Section~\ref{sec:conclusion} concludes.

All the source code in this article has been formalized in Agda
version 2.6.1 using Standard Library 1.3. All source code produced,
including the \LaTeX~source of this article, are available
on-line~\cite{list-rep}.


%%%%%%%%%%%%%%%%%%%%%%%
%% Overview of Agda  %%
%%%%%%%%%%%%%%%%%%%%%%%



\section{An Overview of Agda}\label{sec:agda}

%format String = "\D{String}"
%format Bool = "\D{Bool}"
%format forall = "\D{\forall}"

Agda is a dependently-typed functional programming language based on
Martin-L\"of intuitionistic type theory~\cite{Lof98}.  Function types
and an infinite hierarchy of types of types, |Set l|, where |l| is a
natural number, are built-in. Everything else is a user-defined
type. The type |Set|, also known as |Set0|, is the type of all
``small'' types, such as |Bool|, |String| and |List Bool|.  The type
|Set1| is the type of |Set| and ``others like it'', such as |Set ->
Bool|, |String -> Set|, and |Set -> Set|. We have that |Set l| is an
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
Constructor |[]| builds empty vectors. The cons-operator (|_::_|)
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
This type is called propositional equality. It defines that there is
a unique evidence for equality, constructor |refl| (for reflexivity),
that asserts that the only value equal to |x| is itself. Given a predicate |P : A -> Set|
and a vector |xs|, the type |All P xs| is used to build proofs that |P| holds for all
elements in |xs| and it is defined as:
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
An important application of dependent types is to encode programming languages
syntax. The role of dependent types in this domain is to encode programs that
only allow well-typed and well-scoped terms~\cite{Benton2012}. Intuitively, we encode
the static semantics of the object language in the host language AST's
constructor, leaving the responsibility of checking type safety to the
host's language type checker. As an example, consider the following simple
expression language.
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
Using this data type,\footnote{Agda supports the definition of mixfix operators.
We can use underscores to mark arguments positions.} we can construct expressions
that denote terms that should not be considered well-typed like
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
Agda's type checker will automatically reject a definition which uses the expression |(Num 1) + True|.

%Dependently typed pattern matching is built by using the so-called
%|with| construct, that allows for matching intermediate
%values~\cite{McBride2004}. If the matched value has a dependent type,
%then its result can affect the form of other values. For example,
%consider the following code that defines a type for natural number
%parity. If the natural number is even, it can be represented as the
%sum of two equal natural numbers; if it is odd, it is equal to one
%plus the sum of two equal values. Pattern matching on a value of
%|Parity n| allows to discover if $n = j + j$ or $n = S (k + k)$,
%for some $j$ and $k$ in each branch of |with|.  Note that the
%value of $n$ is specialized accordingly, using information ``learned''
%by the type-checker.
%\begin{spec}
%data Parity : Nat -> Set where
%   Even : forall {n : Nat} -> Parity (n + n)
%   Odd  : forall {n : Nat} -> Parity (S (n + n))
%
%parity : (n : Nat) -> Parity n
%parity = -- definition omitted

%natToBin : Nat -> List Bool
%natToBin zero = []
%natToBin k with (parity k)
%   natToBin (j + j)     | Even = false :: natToBin j
%   natToBin (succ (j + j)) | Odd  = true  :: natToBin j
%\end{spec}

For further information about Agda, see~\cite{Norell2009,Stump16}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% List machine benchmark %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\section{The List Machine Benchmark}\label{sec:list}

The list machine is a simple pointer virtual machine whose values
are empty lists and cons-cells:
\[
a ::= nil\,\mid\,cons(a_1,a_2)
\]
We let meta-variable $a$ to denote an arbitrary value, $v$ denotes a variable
and $l$ a program label. Following common practice, all meta-variables can
appear primed or subscripted. The syntax of the virtual machine instructions are
presented next and their meaning is as usual.
\[
\begin{array}{rcll}
  i & ::=  & \text{jump }l                       & \text{(jump instruction)}\\
    & \mid & \text{branch-if-nil $v$}            & \text{(if $v = nil$ goto $l$)}\\
    & \mid & \text{fetch-field $v$ 0 $v'$}       & \text{(fetch the head of $v$ into $v'$)}\\
    & \mid & \text{fetch-field  $v$ 1 $v'$}      & \text{(fetch the tail of $v$ into $v'$)}\\
    & \mid & \text{cons $v_0$ $v_1$ $v'$}        & \text{(make a cons cell in v')} \\
    & \mid & \text{halt}                         & \text{(finishes execution)}\\
    & \mid & i_1;i_2                             & \text{(sequential composition)}\\
  p & ::=  & l_i \,:\,i\,;\,p                    & \text{(program: sequence of blocks)}\\
    & \mid & \text{end}                          & \text{(end of block list)}\\
\end{array}
\]
Programs are just a sequence of blocks which begin with a unique label. 

Each program variable is assigned a list type which is used to guarantee the safety of execute
fetch-field that demands non-empty list arguments and branch instructions refine the argument type
according to which branch is taken. In order to express such refinements, types are subject to a
subtyping relation. We let the meta-variable $\tau$ denote an arbitrary type. 
\[
\begin{array}{rcll}
  \tau & ::=  & \text{nil} & \text{(type for empty lists)}\\
       & \mid & \text{list }\tau & \text{(lists whose elements have type $\tau$)}\\
       & \mid & \text{listcons }\tau & \text{(non-empty lists of $\tau$)}\\
\end{array}
\]
We let notation $\tau \subset \tau'$
denote the subtyping judgement which is defined as follows.
\[
\begin{array}{ccc}
  \inference{}
            {\tau\subset \tau}
            [refl]
  &
  \inference{}
            {nil \subset \tau}
            [nil]
  &
  \inference{\tau \subset \tau'}
            {list\:\tau\subset list\:\tau'}
            [list]\\\\
  \multicolumn{3}{c}{
  \inference{\tau \subset \tau'}
            {listcons\:\tau\subset list\:\tau'}
            [listcons]} \\\\
            \multicolumn{3}{c}{
            \inference{\tau \subset \tau'}
            {listcons\:\tau\subset listcons\:\tau'}
            [mixed]} \\\\
\end{array}
\]
Basically, the subtyping relation specifies that $nil$ (empty list type) is
subtype of any list type and $listcons\:\tau$ is a subtype of the $list\:\tau$.



\begin{equation}
\inference{}
          {(r, (\iota_1;\iota_2);\iota_3) \xmapsto{p} (r, \iota_1;(\iota_2;\iota_3))}[step-seq]
\end{equation}

\begin{equation}
\inference{r(v) = cons(a_0,a_1)~~~r[v':=a_0]=r'}
          {(r, (\textbf{fetch-field}~v~0~v';\iota)) \xmapsto{p} (r', \iota)}[step-fetch-field-0]
\end{equation}

\begin{equation}
\inference{r(v) = cons(a_0,a_1)~~~r[v':=a_1]=r'}
          {(r, (\textbf{fetch-field}~v~1~v';\iota)) \xmapsto{p} (r', \iota)}[step-fetch-field-1]
\end{equation}

\begin{equation}
\inference{r(v_0) = a_0~~~r(v_1)=a_1~~~r[v':=cons(a_0,a_1)]=r'}
          {(r, (\textbf{cons}~v_0~v_1~v';\iota)) \xmapsto{p} (r', \iota)}[step-cons]
\end{equation}

\begin{equation}
\inference{r(v) = cons(a_0,a_1)}
          {(r, (\textbf{branch-if-nil}~v~l;\iota)) \xmapsto{p} (r, \iota)}[step-branch-not-taken]
\end{equation}

\begin{equation}
\inference{r(v) = nil~~~p(l)=\iota'}
          {(r, (\textbf{branch-if-nil}~v~l;\iota)) \xmapsto{p} (r, \iota')}[step-branch-taken]
\end{equation}

\begin{equation}
\inference{p(l)=\iota'}
          {(r, \textbf{jump}~l) \xmapsto{p} (r, \iota')}[step-jump]
\end{equation}

\begin{equation}
\inference{(r, \iota) \xmapsto{p} (r', \iota')~~~(p, r', \iota')}
          {(p, r, \iota) \Downarrow}[run-step]
\end{equation}

\begin{equation}
\inference{}
          {(p, r, \textbf{halt}) \Downarrow}[run-halt]
\end{equation}

\begin{equation}
\inference{\{\}[\textbf{v}_0:=\text{nil}]=r~~~p(\textbf{L}_0)=\iota~~~(p,r,\iota)\Downarrow}
          {p \Downarrow}[run-prog]
\end{equation}

%\subsection{Typing}

%\subsubsection{Subtyping}

\begin{equation}
\inference{}
          {\tau \subset \tau}[subtype-refl]
\end{equation}

\begin{equation}
\inference{}
          {\text{nil} \subset \text{list}~\tau}[subtype-nil]
\end{equation}

\begin{equation}
\inference{\tau \subset \tau'}
          {\text{list}~\tau \subset \text{list}~\tau'}[subtype-list]
\end{equation}

\begin{equation}
\inference{\tau \subset \tau'}
          {\text{listcons}~\tau \subset \text{list}~\tau'}[subtype-listcons]
\end{equation}

\begin{equation}
\inference{\tau \subset \tau'}
          {\text{listcons}~\tau \subset \text{listcons}~\tau'}[subtype-listmixed]
\end{equation}

%\subsubsection{Instruction typing}

\begin{equation}
\inference{\Pi \vdash_{\text{instr}} \Gamma\{ \iota_1 \}\Gamma'~~~\Pi \vdash_{\text{instr}} \Gamma'\{ \iota_2 \}\Gamma''}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \iota_1 ; \iota_2 \}\Gamma''}[check-instr-seq]
\end{equation}

\begin{equation}
\inference{\Gamma(v) = \text{list}~\tau~~~\Pi(l) = \Gamma_1~~~\Gamma[v:=\text{nil}]=\Gamma'~~~\Gamma' \subset \Gamma_1}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{branch-if-nil}~v~l \}(v: \text{listcons}~\tau,~\Gamma')}[check-instr-branch-list]
\end{equation}

\begin{equation}
\inference{\Gamma(v) = \text{listcons}~\tau~~~\Pi(l) = \Gamma_1~~~\Gamma[v:=\text{nil}]=\Gamma'~~~\Gamma' \subset \Gamma_1}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{branch-if-nil}~v~l \}\Gamma}[check-instr-branch-listcons]
\end{equation}

\begin{equation}
\inference{\Gamma(v) = \text{nil}~~~\Pi(l) = \Gamma_1~~~\Gamma \subset \Gamma_1}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{branch-if-nil}~v~l \}\Gamma}[check-instr-branch-nil]
\end{equation}

\begin{equation}
\inference{\Gamma(v) = \text{listcons}~\tau~~~\Gamma[v':=\tau]=\Gamma'}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{fetch-field}~v~0~v' \}\Gamma'}[check-instr-fetch-0]
\end{equation}

\begin{equation}
\inference{\Gamma(v) = \text{listcons}~\tau~~~\Gamma[v':=\text{list}~\tau]=\Gamma'}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{fetch-field}~v~1~v' \}\Gamma'}[check-instr-fetch-1]
\end{equation}

\begin{equation}
\inference{\Gamma(v_0) = \tau_0~~~~~~~~~\Gamma(v_1) = \tau_1 \\ (\text{list}~\tau_0) \sqcap \tau_1=\text{list}~\tau~~~\Gamma[v:=\text{listcons}~\tau]=\Gamma'}
          {\Pi \vdash_{\text{instr}} \Gamma\{ \textbf{cons}~v_0~v_1~v \}\Gamma'}[check-instr-cons]
\end{equation}

%\subsubsection{Block typings}

\begin{equation}
\inference{}
          {\Pi;\Gamma\vdash_{\text{block}} \textbf{halt}}[check-block-halt]
\end{equation}

\begin{equation}
\inference{\Pi\vdash_{\text{instr}} \Gamma\{\iota_1\}\Gamma'~~~\Pi;\Gamma'\vdash_{\text{block}} \iota_2}
          {\Pi;\Gamma\vdash_{\text{block}} \iota_1;\iota_2}[check-block-seq]
\end{equation}

\begin{equation}
\inference{\Pi(l)=\Gamma_1~~~\Gamma \subset \Gamma_1}
          {\Pi;\Gamma\vdash_{\text{block}} \textbf{jump}~l}[check-block-jump]
\end{equation}

%\subsubsection{Program typings}

\begin{equation}
\inference{\Pi(l)=\Gamma~~~\Pi;\Gamma\vdash_{\text{block}} \iota~~~\Pi\vdash_{\text{blocks}} p}
          {\Pi\vdash_{\text{blocks}} l: \iota;~p}[check-blocks-label]
\end{equation}

\begin{equation}
\inference{}
          {\Pi\vdash_{\text{blocks}} \textbf{end}}[check-blocks-empty]
\end{equation}

\section{Instrinsically-typed syntax}\label{sec:typing}

%format Ty = "\D{Ty}"
%format nil = "\Con{nil}"
%format list = "\Con{list}"
%format listcons = "\Con{listcons}"
%format → = "\rightarrow"
%format ∀ = "\D{\forall}"

In this section we present the design choices and the steps we took to represent the intrinsically-typed syntax for the list-machine benchmark. We present here the Agda code used in our definitions, not necessarily in a strict lexically-scoped order.

Some definitions and rules have been slightly tweaked so that they are accepted by the Agda's type-checker. As a design choice, we dropped all names, using \emph{de Bruijn} indices~\cite{DEBRUIJN72} to represent both \emph{name bindings} for labels and variables. This way, we guarantee that names are always well-scoped.

We started our formalization by defining a type |Ty|, indicating the possible types for the list-machine language.

\begin{spec}
data Ty : Set where
  nil       : Ty
  list      : Ty → Ty
  listcons  : Ty → Ty
\end{spec}

We internalize the list-machine type judgments for blocks and instructions in Agda together with its syntax in such a way where only well-typed terms that satisfy typing judgments have meaning. This approach makes the AST contain both syntactic and semantic properties.

To be well-typed, the list-machine syntax needs to refer to information from two sources: (1) a type context encoded as a list of types to store variable types; and (2) and a program context encoded as a vector\footnote{We use the |Vec| datatype indexed by a |n| which is bound on the module definition and represents the number of labels in the current program.} of type contexts to represent the types of the variables on entry to each basic block.

%format Ctx = "\D{Ctx}"
%format PCtx = "\D{PCtx}"

\begin{spec}
Ctx : Set
Ctx = List Ty
  
PCtx : Set
PCtx = Vec Ctx n
\end{spec}

%format _⊢_⇒_ = "\D{\_\vdash\_\Rightarrow\_}"
%format Block = "\D{Block}"
%format Π = "\V{\Pi}"
%format Γ = "\V{\Gamma}"
%format Γ' = "\V{\Gamma''}"
%format ι = "\V{\iota}"

As we saw in the previous section, the typing rules of the list-machine language were split in two segments, one for instructions and one for blocks. We defined two datatypes (|_⊢_⇒_| and |Block|) to hold the well-typed terms accordingly, representing each judgment of the static semantics as a syntactical constructor. In Agda we use \emph{indexed inductive types} to define a intrinsically-typed syntax.

Both definitions are \emph{parameterized} by a program context and a typing context, and \emph{indexed}\footnote{An index can vary in the result types of the different constructors, while a parameter cannot.} by a resulting typing context. The intuition is that, under program-typing |Π|, the \emph{Hoare triple} |Γ{ι}Γ'| relates precondition |Γ| to postcondition |Γ'|. It is important to note that instead of manipulating syntax directly, the meta-program manipulates structures representing the type judgments as well. Such representation scheme makes the Agda's type-checker allow only well-typed blocks and instructions to be created and manipulated.

The representation of instructions is defined as follows.

%format ∈ = "\D{\in}"
%format ⊓ = "\D{\sqcap}"
%format ~ = "\D{\sim}"
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
  instr-branch-list      : ∀ {τ l Γ' x} → (idx : (x , list τ) ∈ Γ)
                         → Π [ l ]= Γ' → (idx ∷= (x , nil)) ⊂ Γ'
                         → Π ⊢ Γ ⇒ (idx ∷= (x , listcons τ))
  instr-branch-listcons  : ∀ {τ l Γ₁ x}
                         → (idx : (x , listcons τ) ∈ Γ)
                         → Π [ l ]= Γ₁ → (idx ∷= (x , nil)) ⊂ Γ₁
                         → Π ⊢ Γ ⇒ Γ
  instr-branch-nil       : ∀ {Γ₁ l x} → (x , nil) ∈ Γ
                         → Π [ l ]= Γ₁ → Γ ⊂ Γ₁ → Π ⊢ Γ ⇒ Γ
  instr-fetch-0-new      : ∀ {τ x x'} → (x , listcons τ) ∈ Γ
                         → Π ⊢ Γ ⇒ ((x' , τ) ∷ Γ)
  instr-fetch-0-upd      : ∀ {τ τ' x x'} → (x , listcons τ) ∈ Γ
                         → (idx : (x' , τ') ∈ Γ)
                         → Π ⊢ Γ ⇒ (idx ∷= (x' , τ))
  instr-fetch-1-new      : ∀ {τ x x'} → (x , listcons τ) ∈ Γ
                         → Π ⊢ Γ ⇒ ((x' , list τ) ∷ Γ)
  instr-fetch-1-upd      : ∀ {τ τ' x x'} → (x , listcons τ) ∈ Γ
                         → (idx : (x' , τ') ∈ Γ)
                         → Π ⊢ Γ ⇒ (idx ∷= (x' , list τ))
  instr-cons-new         : ∀ {τ τ₀ τ₁ x₀ x₁ x'} → (x₀ , τ₀) ∈ Γ
                         → (x₁ , τ₁) ∈ Γ → list τ₀ ⊓ τ₁ ~ list τ
                         → Π ⊢ Γ ⇒ ((x' , listcons τ) ∷ Γ)
  instr-cons-upd         : ∀ {τ τ₀ τ₁ τ₂ x₀ x₁ x'} → (x₀ , τ₀) ∈ Γ
                         → (x₁ , τ₁) ∈ Γ → (idx : (x' , τ₂) ∈ Γ)
                         → list τ₀ ⊓ τ₁ ~ list τ
                         → Π ⊢ Γ ⇒ (idx ∷= (x' , listcons τ))
\end{spec}

%format _∈_ = "\D{\_\hspace{-2pt}\in\hspace{-2pt}\_}"

In our approach, all name binding is done with statically checked \emph{de Bruijn} indices~\cite{DEBRUIJN72}, a technique for handling binding by using a nameless, position-dependent naming scheme. For example, we use a well-typed \emph{de Bruijn} index |(x , τ) ∈ Γ|, which witnesses the existence of an element |(x , τ)| in |Γ|, as defined by the standard library |_∈_| operator. This technique is well-known for avoiding out-of-bound errors.

\paragraph{Sequencing instructions}{The constructor |instr-seq| can be used to express a sequence of instructions. From the execution of two instructions, it produces a modified typing context containing the changes performed by both instructions.}

\paragraph{Conditional jump}{There are three constructors related to a conditional jump. They are used to perform a jump to a label |l| when the received variable is |nil|. All these constructors type-check the typing context of the intended label with the current typing context. We use |Π [ l ]= Γ₁|, meaning that there exist a typing context |Γ₁| in program typing |Π| related to label |l|. And we use |Γ ⊂ Γ₁| as a proof of subtyping between |Γ| and |Γ₁|.}

\paragraph{Fetching information from list}{There are four constructors which can be used to fetch information from a given list. The constructor |instr-fetch-0-new| receives a non-empty list (|listcons|), and is used to retrieve the head of this list and store it in a fresh new variable. The resulting typing context adds the information about the new variable. Constructor |instr-fetch-0-upd| is also used to retrieve the head element of a list, however storing its value in an existing variable, represented by the \emph{de Bruijn} index |idx : (x' , τ') ∈ Γ|. The constructors |instr-fetch-1-new| and |instr-fetch-1-upd| are similar, fetching the tail of a list instead of the head.}

%format _⊓_~_ = "\D{\_\sqcap\_\sim\_}"

\paragraph{List construction}{The |instr-cons-new| and |instr-cons-upd| constructors are used to create a new list. The first creates a new variable, and the second updates a existing variable. The list is created from two variables, |(x₀ , τ₀) ∈ Γ| and |(x₁ , τ₁) ∈ Γ|, which are represented as \emph{de Bruijn} indices. The type of the new list is defined by the least common supertype\footnote{A complete explanation about the least common supertype can be found in the original list-machine paper~\cite{Appel07}.}, which is defined by the constructor |_⊓_~_|\footnote{The code of this definition is omitted here, but can be found in our online repository.}. The resulting typing context adds information about the newly created list.}

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

Constructor |block-halt| can be used to stop the execution of a given block, |block-seq| has a similar meaning to instruction sequence, and |block-jump| is used to perform a direct jump (without any condition), receiving a label and checking if the current context typing is subtype of the intended one.

%format λ = "\lambda"
%format Program = "\D{Program}"

And finally, a |Program| is a sequence of instruction blocks, each preceded by a label. We use the |All| datatype to express this relationship.

\begin{spec}
Program : PCtx → Set
Program Π = ∀ {Γ'} → All (λ Γ → Block Π Γ Γ') Π
\end{spec}

\section{A definitional interpreter}\label{sec:semantics}

%format Val = "\D{Val}"
%format []v = "\Con{[]v}"
%format _∷_ = "\Con{\_::\_}"
%format _∷v_ = "\Con{\_::v\_}"

\begin{spec}
data Val : Ty → Set where
  nil : Val nil
  []v : ∀ {t} → Val (list t)
  _∷_ : ∀ {t} → Val t → Val (list t) → Val (listcons t)
  _∷v_ :  ∀ {t} → Val t → Val (list t) → Val (list t)
\end{spec}

%format Env = "\D{Env}"

\begin{spec}
Env : Ctx → Set
Env Γ = All (λ (x , τ) → Val τ) Γ
\end{spec}

%format PEnv = "\D{PEnv}"
%format Allv = "\D{Allv}"

\begin{spec}
PEnv : PCtx → Set
PEnv Π = Allv Env Π
\end{spec}

%format run-step = "\F{run\textrm{-}step}"
%format []=⇒lookup = "\F{[]\textrm{=}{\Rightarrow}lookup}"
%format ⊂-Ctx = "\F{\subset\hspace{-3pt}\textrm{-}Ctx}"
%format update-env = "\F{update\textrm{-}env}"
%format lookupA = "\F{lookupA}"
%format <:-val = "\F{\textrm{<:-}val}"
%format list-<:-inv = "\F{list\textrm{-<:-}inv}"
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

\begin{spec}
run-step  : ∀ {Π Γ Γ'} → Fuel → Program Π → Env Γ
          → Block Π Γ Γ' → Maybe (Env Γ')
run-step zero p env b = nothing
run-step (suc n) p env block-halt = just env
run-step (suc n) p env (block-seq (instr-seq i₁ i₂) b) =
  run-step n p env (block-seq i₁ (block-seq i₂ b))
run-step {Π} (suc n) p env (block-seq (instr-branch-list {τ} {i} v l s) b)
  with lookup env v 
... | []v rewrite sym ([]=⇒lookup l) =
  run-step n p (⊂-Ctx s (update-env env v nil)) (lookupA i p)
... | v₁ ∷v v₂ = run-step n p (update-env env v (v₁ ∷ v₂)) b
run-step (suc n) p env (block-seq (instr-branch-listcons v l s) b) =
  run-step n p env b
run-step (suc n) p env (block-seq (instr-branch-nil {l = i} v l s) b)
  rewrite sym ([]=⇒lookup l)
    = run-step n p (⊂-Ctx s env) (lookupA i p)
run-step (suc n) p env (block-seq (instr-fetch-0-new v) b)
  with lookup env v
...| v₁ ∷ v₂ = run-step n p (v₁ ∷ env) b
run-step (suc n) p env (block-seq (instr-fetch-0-upd v v') b)
  with lookup env v
...| v₁ ∷ v₂ = run-step n p (update-env env v' v₁) b
run-step (suc n) p env (block-seq (instr-fetch-1-new v) b)
  with lookup env v
...| v₁ ∷ v₂ = run-step n p (v₂ ∷ env) b
run-step (suc n) p env (block-seq (instr-fetch-1-upd v v') b)
  with lookup env v
...| v₁ ∷ v₂ = run-step n p (update-env env v' v₂) b
run-step (suc n) p env (block-seq (instr-cons-new v₀ v₁ s) b)
  = run-step n p ((<:-val (list-<:-inv (lub-subtype-left
    (lub-of-subtype (lub-subtype-left s)))) (lookup env v₀)
    ∷ <:-val (lub-subtype-right s) (lookup env v₁)) ∷ env) b
run-step (suc n) p env (block-seq (instr-cons-upd v₀ v₁ v' s) b)
  = run-step n p (update-env env v' (<:-val (list-<:-inv
    (lub-subtype-left (lub-of-subtype (lub-subtype-left s))))
    (lookup env v₀) ∷ <:-val (lub-subtype-right s)
    (lookup env v₁))) b
run-step (suc n) p env (block-jump {l = i} l s)
  rewrite sym ([]=⇒lookup l) =
    run-step n p (⊂-Ctx s env) (lookupA i p) 
\end{spec}

\section{Related work}\label{sec:related}

\section{Conclusion}\label{sec:conclusion}



\bibliographystyle{ACM-Reference-Format}
\bibliography{main}
\end{document}
\endinput
