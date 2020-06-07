\documentclass[sigconf]{acmart}

\usepackage{graphicx}
\usepackage[utf8]{inputenc}
\usepackage{amsfonts}
\usepackage{mathtools}
\usepackage{agda}

\AtBeginDocument{%
  \providecommand\BibTeX{{%
    \normalfont B\kern-0.5em{\scshape i\kern-0.25em b}\kern-0.8em\TeX}}}

\setcopyright{acmcopyright}
\copyrightyear{2020}
\acmYear{2020}
%\acmDOI{10.1145/1122445.1122456}

%% These commands are for a PROCEEDINGS abstract or paper.
\acmConference[SBLP '20]{SBLP '20: Brazilian Symposium on Programming Languages}{October 19--23, 2020}{Natal, Brazil}
\acmBooktitle{SBLP '20: Brazilian Symposium on Programming Languages,
  October 19--23, 2020, Natal, Brazil}
%\acmPrice{15.00}
%\acmISBN{978-1-4503-XXXX-X/18/06}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% agda stuff                %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{newunicodechar}
\newunicodechar{γ}{$\gamma$}
\newunicodechar{Γ}{$\Gamma$}
\newunicodechar{τ}{$\tau$}
\newunicodechar{Π}{$\Pi$}
\newunicodechar{→}{$\rightarrow$}
\newunicodechar{⇒}{$\Rightarrow$}
\newunicodechar{∈}{$\in$}
\newunicodechar{∼}{$\sim$}
\newunicodechar{ₗ}{$_l$}
\newunicodechar{ᵣ}{$_r$}
\newunicodechar{∀}{$\forall$}
\newunicodechar{Γ}{$\Gamma$}
\newunicodechar{ℕ}{$\mathbb{N}$}
\newunicodechar{∷}{$::$}
\newunicodechar{₁}{$_1$}
\newunicodechar{₂}{$_2$}
\newunicodechar{₃}{$_3$}
\newunicodechar{₄}{$_4$}
\newunicodechar{ₑ}{$_e$}
\newunicodechar{σ}{$\sigma$}
\newunicodechar{Δ}{$\Delta$}
\newunicodechar{ᴺ}{$^{N}$}
\newunicodechar{∘}{$\circ$}
\newunicodechar{δ}{$\delta$}
\newunicodechar{Σ}{$\Sigma$}
\newunicodechar{λ}{$\lambda$}
\newunicodechar{ᶜ}{$^{c}$}
\newunicodechar{⊎}{$\biguplus$}
\newunicodechar{∧}{$\land$}


\begin{document}

\title{A Certified Interpreter for the List Machine Benchmark}

\author{Samuel Feitosa}
\authornotemark[1]
\email{samuel.feitosa@ifsc.edu.br}
\affiliation{%
  \institution{Departamento de Informática}
  \streetaddress{Instituto Federal de Santa Catarina}
  \city{Caçador}
  \state{Santa Catarina}
  \country{Brazil}
}

\author{Rodrigo Ribeiro}
\email{rodrigo.ribeiro@ufop.edu.br}
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

\section{Introduction}

\section{An Overview of Agda}\label{sec:agda}

Agda is a dependently-typed functional programming language based on
Martin-L\"of intuitionistic type theory~\cite{Lof98}.  Function types
and an infinite hierarchy of types of types, \AgdaDatatype{Set l}, where
\AgdaDatatype{l} is a natural number, are built-in. Everything else is a user-defined
type. The type \AgdaDatatype{Set}, also known as \AgdaDatatype{Set₀}, is the type of all
``small'' types, such as \AgdaDatatype{Bool}, \AgdaDatatype{String} and
\AgdaDatatype{List Bool}.  The type \AgdaDatatype{Set₁} is the type of \AgdaDatatype{Set}
and ``others like it'', such as \AgdaDatatype{Set → Bool}, \AgdaDatatype{String → Set}, and
\AgdaDatatype{Set → Set}. We have that \AgdaDatatype{Set l} is an
element of the type \AgdaDatatype{Set (l+1)}, for every $l \geq 0$. This
stratification of types is used to keep Agda consistent as a logical
theory~\cite{Sorensen2006}.

An ordinary (non-dependent) function type is written \AgdaDatatype{A → B} and a
dependent one is written \AgdaDatatype{(x : A) → B}, where type \AgdaDatatype{B}
depends on \AgdaDatatype{x}, or \AgdaDatatype{∀ (x : A) → B}|. Agda allows the
definition of \emph{implicit parameters}, i.e.,  parameters whose values can be
inferred from the context, by surrounding them in curly braces:
\AgdaDatatype{∀ {x : A} → B}. In order to avoid clutter, we'll omit implicit
arguments from the source code presentation. The reader can safely assume
that every free variable in a type is an implicit parameter.

As an example of Agda code, consider the following data type of
length-indexed lists, also known as vectors.

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  data Vec {A}(A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
\end{code}
\begin{code}[hide]
  infixr 4 _∷_
\end{code}


Constructor \AgdaInductiveConstructor{[]} builds empty vectors. The cons-operator (\AgdaInductiveConstructor{_∷_})
inserts a new element in front of a vector of $n$ elements (of type
\AgdaDatatype{Vec A n}) and returns a value of type \AgdaDatatype{Vec A (suc n)}. The
\AgdaDatatype{Vec} datatype is an example of a dependent type, i.e., a type
that uses a value (that denotes its length). The usefulness of
dependent types can be illustrated with the definition of a safe list
head function: \AgdaFunction{head} can be defined to accept only non-empty
vectors, i.e.,~values of type \AgdaDatatype{Vec A (suc n)}.
\begin{code}
  head : ∀ {A n} → Vec A (suc n) → A
  head (x ∷ xs) = x
\end{code}
In \AgdaFunction{head}'s definition, constructor \AgdaInductiveConstructor{[]} is not used. The
Agda type-checker can figure out, from \AgdaFunction{head}'s parameter type,
that argument \AgdaInductiveConstructor{[]} to \AgdaFunction{head} is not type-correct.

Another useful data type is the finite type, \AgdaDatatype{Fin}\footnote{Note that Agda supports the overloading of data type constructor names.
Constructor \AgdaInductiveConstructor{zero} can refer to type \AgdaDatatype{ℕ} or \AgdaDatatype{Fin}, depending on the
context where the name is used.}, which is defined in
Agda's standard library as:

\begin{code}
  data Fin : ℕ → Set where
    zero : ∀ {n} → Fin (suc n)
    suc : ∀ {n} → Fin n → Fin (suc n)
\end{code}
Type \AgdaDatatype{Fin n} has exactly \AgdaDatatype{n} inhabitants
(elements), i.e., it is isomorphic to the set $\{0,...,n - 1\}$.
An application of such type is to define a safe vector
lookup function, which avoids the access of invalid positions.
\begin{code}
  lookup : ∀ {A n} → Fin n → Vec A n → A
  lookup zero (x ∷ _) = x
  lookup (suc idx) (_ ∷ xs) = lookup idx xs
\end{code}
Thanks to the propositions-as-types principle,\footnote{It is also known as
  Curry-Howard ``isomorphism''~\cite{Sorensen2006}.} we can interpret
types as logical formulas and terms as proofs. An example is the
representation of equality as the following Agda type:

\begin{code}
  data _≡_ {l}{A : Set l}(x : A) : A → Set where
    refl : x ≡ x
\end{code}

This type is called propositional equality. It defines that there is
a unique evidence for equality, constructor \AgdaInductiveConstructor{refl} (for reflexivity),
that asserts that the only value equal to \AgdaInductiveConstructor{x} is itself.
Given a predicate \AgdaDatatype{P : A → Set} and a vector \AgdaInductiveConstructor{xs}, the
type \AgdaDatatype{All P xs} is used to build proofs that \AgdaDatatype{P} holds for all
elements in \AgdaDatatype{xs} and it is defined as:
\begin{code}
  data All {A n}(P : A → Set) : Vec A n →  Set where
     [] : All P []
     _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)
\end{code}
The first constructor specifies that \AgdaDatatype{All P} holds for the empty vector and
constructor \AgdaInductiveConstructor{_∷_} builds a proof of \AgdaDatatype{All P (x :: xs)} from proofs of
\AgdaDatatype{P x} and \AgdaDatatype{All P xs}. Since this type has the same structure of vectors,
some functions on \AgdaDatatype{Vec} have similar definitions for type \AgdaDatatype{All}. As an example
used in our formalization, consider the function \AgdaFunction{lookup}, which extracts a
proof of \AgdaDatatype{P} for the element at position \AgdaDatatype{v : Fin n} in a \AgdaDatatype{Vec}:
\begin{spec}
  lookup : ∀ {A n P x}{xs : Vec A n} → Fin n → All P xs → P x
  lookup zero (px ∷ _) = px
  lookup (succ idx) (_ ∷ pxs) = lookup idx pxs
\end{spec}
An important application of dependent types is to encode programming languages
syntax. The role of dependent types in this domain is to encode programs that
only allow well-typed and well-scoped terms~\cite{Benton2012}. Intuitively, we encode
the static semantics of the object language in the host language AST's
constructor, leaving the responsibility of checking type safety to the
host's language type checker. As an example, consider the following simple
expression language.
\begin{spec}
  data Expr : Set where
    True False : Expr
    Num : ℕ → Expr
    _∧_ _+_ : Expr → Expr → Expr
\end{spec}
Using this data type,\footnote{Agda supports the definition of mixfix operators.
We can use underscores to mark arguments positions.} we can construct expressions
that denote terms that should not be considered well-typed like
\AgdaFunction{(Num 1) + True}. Using this approach, we need to specify the static semantics
as another definition, which should consider all possible cases to avoid the
definition of ill-typed terms.

A better approach is to combine the static semantics and language syntax into
a single definition, as shown below.

\begin{code}
  data Ty : Set where
    Nat Bool : Ty

  data Expr : Ty → Set where
    True False : Expr Bool
    Num : ℕ → Expr Nat
    _∧_ : Expr Bool → Expr Bool → Expr Bool
    _+_ : Expr Nat → Expr Nat → Expr Nat
\end{code}

In this definition, the \AgdaDatatype{Expr} type is indexed by a value of type \AgdaDatatype{Ty} which
indicates the type of the expression being built. In this approach, Agda's
type system can enforce that only well-typed terms could be written.
Agda's type checker will automatically reject a definition which uses the expression
\AgdaFunction{(Num 1) + True}.

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
\bibliography{sample-base}
\end{document}
\endinput
