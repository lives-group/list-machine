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
\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
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


\begin{abstract}
This is the abstract...
\end{abstract}

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


\section{Introduction}

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


Another useful data type is the finite type, |Fin|\footnote{Note that Agda supports the overloading of data type constructor names.
Constructor |zero| can refer to type |Nat| or |Fin|, depending on the
context where the name is used.}, which is defined in
Agda's standard library as:

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
proof of |P| for the element at position |v :: Fin n| in a |Vec|:
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

\bibliographystyle{ACM-Reference-Format}
\bibliography{main}
\end{document}
\endinput
