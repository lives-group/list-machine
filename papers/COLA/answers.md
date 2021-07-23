# Answers to reviewers


Reviewer 1
==========

a. "The article is very well written and the contribution is significant to the area. When compared to the SBLP 2020 article, the extension suffices the criteria for a long article."

Answer: Thank you!

b. "If I'm not mistaken, the `data Val` presented in 355 embeds the subtyping of values. Have you considered compressing it into just 
 the nil and cons constructor, and then use subtyping to derive the other two? Does it complicate things?"
 
Answer: Yes, the type `Val` embeds the subtyping relation and we
decided to use this  encoding to reduce the complexity of the value 
type casting function definition.

Thanks!


c. "Something that isn't mentioned is how to trust the proof. And I don't mean the checking of Agda, I mean the philosophical aspect of constructing a proof of soundness for a language. If we write incorrect typechecking rules, we might trivialize soundness: if no program can be typechecked, then every program that typechecks is sound (imagine adding a hypothesis `False -> ...` to every rule). This problem is not inherent to the intrinsic approach, but there is an important part in building a soundness proof that is checking the rules "makes sense". Since we've done extrinsically proofs for years, we sort of know where to eye a proof. How would this compare with following the intrinsic approach? I understand this is not really related to the benchmark, but since part of the conclusion is to sell this approach, I think it is relevant to have a comment on this matter."

Answer: The main advantage of the intrisinc approach to prove type soundness 
in proof assistants is to avoid dealing the stuck states in the semantics, which
are simply ruled out by the underlying type system (program syntax) by construction. 

Checking if the rule definitions do make sense is quite similar to the 
conventional approach, since in the intrinsically typed version we just 
combine the syntax and the type system of the language in one single 
definition. 

Thanks!


d. "Typos and bibliography issues:

 - Near 535: the top and bottom are prefixed with a "`" that isn't in the figures below.
 - Bibs [8,21]: missing year.
 - Bibs [16,17] (and probably others): names are in lowercase (coq, agda)."
 
 Answer: Fixed. Thanks!


Reviewer 2
==========

a. " The formalization in Agda (github cloned as of 10th of May) has
several postulates about the calculation of glb and lub for contexts
and this is used in the type-checker and the interpreter. I think this
should be clearly stated with an explanation of the difficulties on
trying to define them. Moreover, are there examples of programs that
cannot run or input programs that cannot be type-checked? Less
important, how would affect this the LOC count?"

Answer: We fixed this issue by completely implemented all these postulates
with the exception of a lemma used by the equation of value casting function 
for continuation types. As far as we know, this equation cannot be proved 
without resorting to a semantic formulation, as done by Appel's solution based 
on his modal logic inspired model. 

Some questions that might arise are about the safety of adding this postulate 
and why not follow Appel's path on a semantic-based formulation. We believe that
Appel's solution to the version 2.0 of the list-machine benchmark follows a completely 
different path from our work, since it does not rely on dependently typed 
syntax for list-machine programs. Appel's formalization uses a shallow embedding of 
programs based on his modal logic model, which allows expressing the contravariance
of context subtyping relation at a semantic level. Since this approach is radically 
different from using intrinsically-typed syntax for proving typed soundness by
definitional interpreters, we postulate the corresponding lemma present in Appel's 
solution.

b. "It might be worth a discussion of literature about the «internalist
approach» in the mechanization of programming languages in dependently
typed languages. You might look into Alberto Pardo's contributions on
this as an entry point to the literature."

Answer: We include the following text about Pardo's work: 

"Another application of intrisincally-typed syntax is Pardo's et. al. work on correct-by-construction 
compilers~\cite{PardoGPV18}. The approach used by the authors is to index the syntax of 
a language with its types and semantics in order to automatically derive a correctness proof for the
compiler. Authors apply their metodology in an arithmetic expression languages and a imperative
language with top-level variables, sequencing and looping statements."

Thanks!


c. "In l. 255 you claim that you use de Bruijn indices but in fact you are
using an explicit proof «(x,τ) ∈ Γ» to assure that x is in the domain
of Γ. If you were using de Bruijn indices instead of «(x,τ) ∈ Γ» you
would have something like «Γ [ x ]= τ»"

Answer: The main reason for carrying names in our typing contexts was to ease
the task of proving the soundness of our type checker. While contexts were 
carrying names, variables were completely represented by list membership proof 
(typed de Bruijn indices), which guarantee that they are position and not
name based. We have modified our code to completely eliminate names from 
contexts and changed our type checker formalization.


d. "The duplication of some rules seems unnecessary and, I think, reveals
a more important issue: you don't discuss your implementation of
Γ[v:=τ]. It seems that you can define such an operator and let it
handle wheter v∈dom(Γ) or not."

Answer: 


e. "It would be nice if your formalization includes a Samples.agda module
with, at least, the samples from the benchmark."

Answer: Thanks for suggesting this. We added a file with the example program
from the benchmark.


f. "You didn't mention the 15th item of the benchmark: have you considered
using literate Agda to produce the paper?"

Answer: Agda compiler does support literate programming. However, we think that 
it does not have all the ingredients to ease the task of typesetting latex as 
the coq-doc tool or even lhs2tex, which we use to build our paper. We add the 
following text about this item:

"
\textbf{Generate~\LaTeX.} Agda's compiler does have a limited support for typesetting~\LaTeX code.
        However, we find it lacking some important features like omitting code from typesetted output
        and use~\LaTeX math-commands instead of unicode characters for mathematical symbols."

g. "- l 27. It doesn't sound right to say: "... we contribute" and then
start each sentence in the enumeration with "We ...". Perhaps you can
say, "Let us summarize our contributions."

Answer: Fixed. Thanks!

h. "l 113. You might want to separate the explanation of intensional
  equality (_≡_ and refl) from the explanation about All."
  
Answer: Fixed. Thanks!

i. "l 163. «list» should be «least»"

"Each program variable is assigned to a list type, which is used to guarantee the 
safety when executing fetch-field instructions that demands non-empty list 
arguments."

Answer: Fixed. Thanks!

j. "l 178. The lub operator in the typing-rule cons is upside-down. Or
  perhaps you use the meet-like operator to refer to the lub, in which
  case you should explain you do that."
  
Answer: We follow Appel's et. al. notation used in his Journal of Automated Reasoning paper.
We apologize for the confusion.

k. "l 186. There is an overflow."

Answer: Fixed. Thanks!

l. "l 211. «List (String × Ty)» should be «List (ℕ × Ty)»"

Answer: Fixed. Thanks!

m. "Remove all the unused code (including superflous imports)."

Answer: We remove all unused code and imports. Thanks!

n. "l 332. typo «t1 <: t3» should be «t1 <: t4»"

Answer: Fixed. Thanks!

o. "l 515. «with a bottom and top» should be «with bottom and top»"

Answer: Fixed. Thanks!

p. "l 535~540. «The other rule stabishes» should be «The other rule
  establishes»"
  
Answer: Fixed. Thanks!

q. "l 538. «notation to code and are omitted for brevity.» can finish in
«notation»."

Answer: Fixed. Thanks!


r. "l 546. «jumps, Appel and Leroy. approach» should be «jumps, Appel
  and Leroy's approach»".
  
Answer: Fixed. Thanks!

s. "I don't think you need to repeat once and again that some parts
can be found in the repository."

Answer: We removed such repetitions. Thanks! 

t. "«⊨_prog p : Π» should be «⊢_prog p : Π» in Tasks 3, 5 and 9."

Answer: We follow Appel's notation for the task names. In order to be 
consistent to the original benchmark proposal, we keep the original.

u. "l 744. It is a bit odd to start a sentence with a reference, please
rephrase it."

Answer: Fixed. Thanks.

v. "If I haven't misunderstood the issue on the definition of the lub
for contexts is that your rule doesn't contemplate that a list and
some permutation of it are "compatible". In fact, let
Γ=[(0,nil),(1,nil)] and Γ'=[(1,nil),(0,nil)] can you prove Γ ∩ Γ' ~ Γ?

Perhaps it's the same sympton about Γ[v:=τ] mentioned earlier."

Answer: Our previous version used names in contexts only to ease the 
task of proving soundness for our type checker. We changed our code 
to completely remove names and now it only uses typed de Bruijn indices 
(list membership proofs) to denote variables. In such setting,  
the type system judgements are preserved under permutations.


Reviewer 3
==========


1. "Parts of the paper seem to address a general (non-Agda) audience, whereas other parts of the paper assume intimate familiarity with Agda.  I think the paper should be made more accessible to non-Agda people, or (at least) state explicitly what is assumed on behalf of the reader and be consistent in what is explained and what is not."

Answer: We apologize for this inconvenience and take your suggestions into account to improve 
the writing of our work. Thanks for your time!

2. "The paper is not sufficiently self-contained.  S9 reports on the numbers that compare Appel et al.'s benchmark solutions with the approach in the submitted manuscript; but the section does not explain what each bulletpoint really covers, or in many cases where the differences in code sizes stems from (see detailed comments below).  This is the main contribution of the paper, and shouldn't require the reader to read the Appel et al. [12] paper and the source code that isn't linked from the paper to make to draw his/her own conclusions."

Answer: We expanded these descriptions based on your suggestions. Thanks!


3. "I had to read Appel et al.'s paper [12] to make sense of the newly added S8 (which is also full of typos).  I think this section needs major revision."

Answer: We apologize for this. This section was revised and we hope that it is ok. Thanks!

4. "There are multiple typos in rules, and the corresponding Agda code is sometimes omitted, making it hard to assess whether the code really corresponds to Appel et al. [12].  From what I see, these seem to be just typos, but the authors did not provide a URL where I could access the code, so I don't know."

Answer: The link for the our code repository is given as a reference at 
the end of the last sentence of our work introduction section. We added the corresponding citation
everywhere we mention the code repository.

Thanks!

5. "It should be possible to understand the contributions without having read the rest of the paper."

Answer: We tried to improve the writing of our paper. Thanks for your careful reading.


6. "I found reading this section a slog.

It is not obvious how these examples are relevant for the rest of the paper.

Your Agda code is using a different casing convention for constructors from the rest of the paper."

Answer: The reason of Agda code examples presented in this section is to 
provide a quick introduction to its syntax. We disagree that the code 
is not relevant, since:
* We use natural numbers in Peano notation everywhere in our formalization.
* We use Vectors (length-indexed lists) to represent the set of initial 
context typings for the blocks that denote a complete program.
* Finite types (the `Fin` type) are used to represent program labels in 
jump instructions
* Finally, the inductive predicate `All` is used to form a complete program 
indexed by the length-indexed list of each block initial type environment.

We improve the Agda introduction section by adding more examples about equality and rewriting.


7. "General: dives straight into describing intrinsically-typed syntax.  What is the relationship with the list-machine benchmark?"

Answer: We added the following sentence in order to link the section about typed-syntax and 
the main contributions of our paper: 

Before considering our solution to encode list-machine
programs as instrisincally-typed syntax, we review this approach in a reduced example.

8. "You used mixfix operators in S2 as well, so this footnote should occur earlier."

Answer: We move it to Section 2, where the first use of mixfix operators 
occur. Thanks! 

9. "I would recommend to say explicitly that this entire section is recalling object language syntax and typing rules from Appel et al. [12]."

Answer: Fixed. Thanks!

10. "I would also recommend to use figures, as I found myself leafing back and forth between the syntax and typing rules, and found them hard to locate."

Answer: We changed the paper source to use figures for the typing rules.
Thanks for the suggestion.

11. "p 8 top: their meaning is as usual"

Answer: We removed that sentence. Thanks!

12. "Your subtyping rules differ in naming and semantics from Appel et al:
- the nil rule is wrong (but you seem to have encoded the correct rule from Appel et al. in Agda [l315]).
- the naming of the mixed rule and listcons rule is swapped compared with Appel et al.

Please use the same rule names as Appel et al.  Makes it much easier to compare."

Answer: Fixed. Thanks!


13. "The list common supertype => _Least_ common supertype."

Answer: Fixed. Thanks!

14. "Why not use ⊔ like Appel et al.?"

Answer: Fixed. Thanks!

15. "l 174: The type system proposed by Appel and Leroy [12]
Appel et al.  (Dockins is second co-author.)
This occurs many times in the paper."

Answer: Fixed. Thanks! 

16. "It's confusing that type environments contain names since you say that you use de Bruijn indices for names."

Answer: In our submitted formalization, we use names just to ease the type-checker correctness 
proof. The names did not play any rule in variable representation. In order to avoid confusion, 
we modify our code to use de Bruijn indices and completely omit names.

17. "> l 212-ish: PCtx = Vec Ctx n

Where does the n come from?

I was confused as to why you use a Vec instead of List.  I presume that you're going to use Fin n for labels?  Please explain."


Answer: Yes, you correctly figure it out. We 
use vector to denote the set of program contexts
and `Fin` type to encode program labels. The `n` is a
paramater, which we erroneously omitted. Thanks!

18. "l220: Such representation scheme makes the Agda's type-checker

Such _a_ representation scheme makes ~~the~~ Agda's type checker"

Answer: Fixed. Thanks!

19. "Why is it necessary to have two versions of 
the instr-fetch-0-* rules?  I'd have expected 
instr-fetch-0-new to suffice."

Answer: We follow this design decision in order to ease the development of the type checker and interpreter.


20. "Can you say something about how your ⊓ compares with the definition of ⊔ in, e.g., the Coq code of Appel et al.?"

Answer: We fix our notation to follow Appel et. al. convention.

21. "What do you mean by "type environments"?  The previous sentence talks about plain environments.  You're using the terminology "typing context" in other places."

Answer: We fix the reference "type environment"
to typing context. Thanks!

22. "l 372: Env Γ = All (λ(x , τ) → Val τ) Γ

It's still puzzling why identifiers occur in typing contexts."

Answer: We changed our code to omit the names in environments. Names used in environments 
just play a role in the correctness of the type checker. They are not used in our
interpreter. Thanks for your suggestion.

23. "Where is the online repository?"

Answer: The link for the online repository 
was presented as a citation in the last 
sentence of the article introduction section. 
We included the citation in all places where
we mention the repository. 
Thanks for pointing this issue.

24. l 413: instr-branch-nil {l = i} v l s

It looks odd that you have two variables named l 
in this pattern.  Is this really accepted by Agda?

Answer: Yes, this is accepted by Agda. The 
first occurrence of l is being renamed to i.
In order to avoid confusion, we changed these 
kind of pattern matching in our code and in 
the paper.

Thanks!

25. "l 414: []=⇒lookup l

What does this lemma say, and why is it needed here?

The "rewrite" feature is quite unfamiliar to non-Agda people.  Again, it seems odd that you have an Agda background section (S2) that gives a very basic introduction to Agda but then assume familiarity with sophisticated Agda features in the rest of the paper.  I would propose to add a sentence, or maybe a footnote, whenever you use a feature that would cause non-Agda people to stumble."

Answer: The lemma []=⇒lookup allows the rewriting
of a predicate for vector lookup ([]=⇒) by a 
equality using the function lookup. 
We add the following sentence when we first use the function []=⇒lookup: 

We use
Agda's standard library function |[]=⇒lookup|:
\begin{spec}
[]=⇒lookup : ∀ {px : P x} {pxs : All P xs} {i : x ∈ xs} →
             pxs [ i ]= px →
             lookupA pxs i == px
\end{spec}
which rewrites a lookup predicate (|pxs [ i ]= px|) into an equality using the |lookupA|
function, |lookupA pxs i == px|.


In order to improve our Agda introductory section, we
will add an example using the rewrite syntax.

Thanks for your suggestions!

26. "What is a CheckedInstr?

Is your approach to type checking similar to the approach in the Agda docs?  https://agda.readthedocs.io/en/v2.6.1.3/language/syntactic-sugar.html#example

That approach enforces an additional safety property of type checking: a type checker does not lose any structure that was in the original, untyped, AST.

The one case you show seems to correspond to the approach in the Agda docs.  Cite it, or (better) cite Ulf Norell's Agda tutorial where this approach seems to have first occurred.

There's code in S8 that assumes familiarity with the code that you're not showing or even discussing in this section. :("

Answer: Yes, our approach to ensure the correctness of the type checker is the same 
as in Ulf Norell's tutorial. We add more code and explained more details of how the 
correctness of the type-checker is proved.

27. "S8.1 is hard to read and full of typos.  Please proof-read.  I would recommend to stick closer to the explanations Appel et al. give for indirect jumps.  I had to read their paper to make sense of what you wrote in S8.1.  I think this section needs rewriting.

S8.1:
- Why are none of the rules in this section named?
- I think you mean ⊂ instead of <: in all the rules of this section.
- Some of the rules in this section use ⊔ and some use ⊓.  Which is it?
- l 536: ommited -> mitted
- l 537: rules -- Some of these rules seem to follow from the commutativity rules you say you omit and the rules you gave earlier in the section?
- p 25 top: The last rule show -> The last rule show_s_

Answer: We will answer each of these considerations separatedly.

- "Why are none of the rules in this section named?" => We add names to each rule presented in 
this section. Thanks!

- "I think you mean ⊂ instead of <: in all the rules of this section." => We double checked the 
rules with Appel's paper and now we belive that they are ok. Thanks!

- "I think you mean ⊂ instead of <: in all the rules of this section." => This section extends
the definition of least upper bound for types and provides the definition of greatest lower bounds.
This is necessary in order to express the contravariance of the continuation type.

- "l 536: ommited -> mitted" => Fixed. Thanks!

- "l 537: rules -- Some of these rules seem to follow from the commutativity rules you say you omit and the rules you gave earlier in the section?" => We provide complete definitions for the least upper
bound relation on types. The additional rules just extends the previously defined ones. Thanks!

- "p 25 top: The last rule show -> The last rule show_s_" => Fixed. Thanks!

28. "- l 588: the "-- same code from before" comment refers to code that you have not shown before.  In general, all of this code is hard/impossible to understand because you do not explain your setup in S7."

Answer: We tried to improve the explanations by giving more details on our implementation. Thanks!

29. "Numbers look great.  You should provide a URL to your repository so readers can validate them.

You should also provide a summary of what the Twelf and Coq developments do and how/why the numbers differ in your approach for each of the 14 bulletpoints that this section discusses."

Answer: We added the reference for our code repository on every mention of it.

30. "6. State properties of the least common supertype. This is trivial, since it is just a matter to encode the desired properties as Agda function types

I don't understand what this means?  Show some code?"

Answer: The idea is that representing the propreties of the least common supertype is just 
a matter of representing is corresponding formula as a Agda function type. Since Agda is 
based on intuitionistic type theory, types can be interpreted as logical formulas because of
the Curry-Howard isomorphism.

31. "> 10. Asymptotically efficient algorithm. Our current implementation of the type-checker takes quadratic time.

Your explanation seems to suggest you do not implement a symptotically efficient algorithm, but the number in the table suggests you do?"

Answer: Our algorithm could be more efficient by using appropriate data structures like red-black
trees. However, the support for such types in Agda standard library is quite limited and we decided 
to use its support for lists and vectors. 


Final remarks
=============

We have modified the paper, technical report and code repository in order to address all considerations from the anonymous reviewers. Finally, we would like to thank you for your careful reading and suggestions that have helped us to improve the presentation of our results.

