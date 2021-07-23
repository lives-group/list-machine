Reviewer 1: Summary

The article describes the list-machine benchmark using an intrinsically-typed approach. 
The benchmark helps weighing in different systems and approaches when performing the
validation of a machine. The authors incorporate a new actor in the comparison: Agda using 
a strict type discipline in which no bad program can be written, since the syntax embeds the
typechecking validation. The comparison with the previous approaches shows that several 
proofs are indeed shorter using this approach. The article extends the work presented at 
SBLP 2020 with jump instructions.

Conclusion

The article is very well written and the contribution is significant to the area. When compared 
to the SBLP 2020 article, the extension suffices the criteria for a long article. To this reviewer 
the article can be published as is, except for a few minor issues in the Bibliography section 
(see below). This said, I'd appreciate if something can be said about the following points:

 1. If I'm not mistaken, the `data Val` presented in 355 embeds the subtyping of values. Have you considered compressing it into just 
 the nil and cons constructor, and then use subtyping to derive the other two? Does it complicate things?

 2. Something that isn't mentioned is how to trust the proof. And I don't mean the checking of Agda, I mean the philosophical aspect of constructing a proof of soundness for a language. If we write incorrect typechecking rules, we might trivialize soundness: if no program can be typechecked, then every program that typechecks is sound (imagine adding a hypothesis `False -> ...` to every rule). This problem is not inherent to the intrinsic approach, but there is an important part in building a soundness proof that is checking the rules "makes sense". Since we've done extrinsically proofs for years, we sort of know where to eye a proof. How would this compare with following the intrinsic approach? I understand this is not really related to the benchmark, but since part of the conclusion is to sell this approach, I think it is relevant to have a comment on this matter.

Typos and bibliography issues:

 - Near 535: the top and bottom are prefixed with a "`" that isn't in the figures below.
 - Bibs [8,21]: missing year.
 - Bibs [16,17] (and probably others): names are in lowercase (coq, agda).



Reviewer 2: The formalization in Agda (github cloned as of 10th of May) has
several postulates about the calculation of glb and lub for contexts
and this is used in the type-checker and the interpreter. I think this
should be clearly stated with an explanation of the difficulties on
trying to define them. Moreover, are there examples of programs that
cannot run or input programs that cannot be type-checked? Less
important, how would affect this the LOC count?

It might be worth a discussion of literature about the «internalist
approach» in the mechanization of programming languages in dependently
typed languages. You might look into Alberto Pardo's contributions on
this as an entry point to the literature.

In l. 255 you claim that you use de Bruijn indices but in fact you are
using an explicit proof «(x,τ) ∈ Γ» to assure that x is in the domain
of Γ. If you were using de Bruijn indices instead of «(x,τ) ∈ Γ» you
would have something like «Γ [ x ]= τ»

The duplication of some rules seems unnecessary and, I think, reveals
a more important issue: you don't discuss your implementation of
Γ[v:=τ]. It seems that you can define such an operator and let it
handle wheter v∈dom(Γ) or not.

It would be nice if your formalization includes a Samples.agda module
with, at least, the samples from the benchmark.

You didn't mention the 15th item of the benchmark: have you considered
using literate Agda to produce the paper?

Minor remarks:

- l 27. It doesn't sound right to say: "... we contribute" and then
start each sentence in the enumeration with "We ...". Perhaps you can
say, "Let us summarize our contributions."
- l 113. You might want to separate the explanation of intensional
  equality (_≡_ and refl) from the explanation about All.
- Move the sentence about more information on agda to the end of section 2.
- l 163. «list» should be «least»

- l 178. The lub operator in the typing-rule cons is upside-down. Or
  perhaps you use the meet-like operator to refer to the lub, in which
  case you should explain you do that.

- l 186. There is an overflow.
- l 211. «List (String × Ty)» should be «List (ℕ × Ty)»
- Remove all the unused code (including superflous imports).
- l 332. typo «t1 <: t3» should be «t1 <: t4»
- l 515. «with a bottom and top» should be «with bottom and top»
- l 535~540. «The other rule stabishes» should be «The other rule
  establishes»
- l 538. «notation to code and are omitted for brevity.» can finish in
«notation».
- l 546. «jumps, Appel and Leroy. approach» should be «jumps, Appel
  and Leroy's approach»
- I don't think you need to repeat once and again that some parts
can be found in the repository.
- «⊨_prog p : Π» should be «⊢_prog p : Π» in Tasks 3, 5 and 9.
- You mention that you «implemented the algorithm which shows that
this relation is indeed a function.» In fact, you need to prove
anti-symmetry to conclude that the relation is a function.
- l 744. It is a bit odd to start a sentence with a reference, please
rephrase it.

About the formalization:

- Since you know that lub is commutative, you can avoid the repetitive
  proof for lub-subtype-right:

lub-subtype-right : ∀ {τ₁ τ₂ τ₃} → τ₁ ⊓ τ₂ ~ τ₃ → τ₂ <: τ₃
lub-subtype-right t = lub-subtype-left (lub-comm t)

- Perhaps it is interesting to note that the sub-typing relation
  for version1 is anti-symmetric. Is it so for version2? I expect so.

- If I haven't misunderstood the issue on the definition of the lub
for contexts is that your rule doesn't contemplate that a list and
some permutation of it are "compatible". In fact, let
Γ=[(0,nil),(1,nil)] and Γ'=[(1,nil),(0,nil)] can you prove Γ ∩ Γ' ~ Γ?

Perhaps it's the same sympton about Γ[v:=τ] mentioned earlier.






Reviewer 3: # General Notes

This paper builds an intrinsically typed definitional interpreter for the List Machine Benchmark of Appel et al., and reports numbers that suggest that the approach has superior conciseness.

The paper is an extended version of an SBLP paper by the same title.  Compared with the original paper, the new manuscript adds support for indirect jumps, as specified in the version 2.0 of the list machine benchmark.

Being familiar with, e.g., the PLFA book by Wadler and Kokke, I am not surprised that  the intrinsically typed approach is more concise than extrinsically typed approach.  Still, I think it is useful to compare the approaches by using the benchmark of Appel et al. which is designed for this purpose.

While I think that there are some useful contributions in the work that the authors report upon I have some serious concerns about the presentation in the current paper.  My major concerns are:

- Parts of the paper seem to address a general (non-Agda) audience, whereas other parts of the paper assume intimate familiarity with Agda.  I think the paper should be made more accessible to non-Agda people, or (at least) state explicitly what is assumed on behalf of the reader and be consistent in what is explained and what is not.

- The paper is not sufficiently self-contained.  S9 reports on the numbers that compare Appel et al.'s benchmark solutions with the approach in the submitted manuscript; but the section does not explain what each bulletpoint really covers, or in many cases where the differences in code sizes stems from (see detailed comments below).  This is the main contribution of the paper, and shouldn't require the reader to read the Appel et al. [12] paper and the source code that isn't linked from the paper to make to draw his/her own conclusions.

- I had to read Appel et al.'s paper [12] to make sense of the newly added S8 (which is also full of typos).  I think this section needs major revision.

Minor:

- There are multiple typos in rules, and the corresponding Agda code is sometimes omitted, making it hard to assess whether the code really corresponds to Appel et al. [12].  From what I see, these seem to be just typos, but the authors did not provide a URL where I could access the code, so I don't know.

- The paper does not cite relevant papers from which they borrow their techniques from (especially in S7 -- see my detailed comments below).

- I have several additional concerns about presentation.  See the detailed comments below.

For these reasons, I recommend a major revision before the paper is ready for publication in a journal.


# S1

It should be possible to understand the contributions without having read the rest of the paper.

For example:

> We provide a provably correct implementation for testing the subtyping relation and to calculate the least common supertype of two input types for the machine registers.

Unclear what the problem is at this point in the paper.


# S2

I found reading this section a slog.

It is not obvious how these examples are relevant for the rest of the paper.

Your Agda code is using a different casing convention for constructors from the rest of the paper.


# S3

General: dives straight into describing intrinsically-typed syntax.  What is the relationship with the list-machine benchmark?

> l135: For this paper, we assume a basic knowledge of functional programming and Agda.

What is the point of S2 then?

> Footnote 4

You used mixfix operators in S2 as well, so this footnote should occur earlier.


# S4

I would recommend to say explicitly that this entire section is recalling object language syntax and typing rules from Appel et al. [12].

I would also recommend to use figures, as I found myself leafing back and forth between the syntax and typing rules, and found them hard to locate.

> p 8 top: their meaning is as usual

Drop sentence?  Doesn't help readers who haven't seen it before, nor readers that have.

> l 161: Each program variable is assigned to a list type

I found this statement cryptic, as I hadn't seen any object language types at this point.  Consider reformulating and moving the syntax of types up so it becomes clearer that you are talking about the typing of variables.

> l 162-ish: nil rule and mixed rule

Your subtyping rules differ in naming and semantics from Appel et al:
- the nil rule is wrong (but you seem to have encoded the correct rule from Appel et al. in Agda [l315]).
- the naming of the mixed rule and listcons rule is swapped compared with Appel et al.

Please use the same rule names as Appel et al.  Makes it much easier to compare.

> l 164-ish: The list common supertype

_Least_ common supertype.

Why not use ⊔ like Appel et al.?

> l 174: The type system proposed by Appel and Leroy [12]

Appel et al.  (Dockins is second co-author.)

This occurs many times in the paper.

> l 180: block-seq

Please type set your rule references in a way that it matches the rules (i.e., not italic for one and roman for the other).

> p 11 top

The rules for "blocks" should be adjacent.

> Inspired by the presented typing rules, in the next section, we define an intrinsically- 185 typed syntax for list-machine programs which ensures that only well-typed programs can be built.

Why only "inspired by"?  The abstract of your paper seems to make a stronger claim.


# S5

> l 210: Ctx = List (String × Ty)

It's confusing that type environments contain names since you say that you use de Bruijn indices for names.

> l 212-ish: PCtx = Vec Ctx n

Where does the n come from?

I was confused as to why you use a Vec instead of List.  I presume that you're going to use Fin n for labels?  Please explain.

> l220: Such representation scheme makes the Agda's type-checker

Such _a_ representation scheme makes ~~the~~ Agda's type checker

> l 223-ish: The representation of instructions is defined as follows.

Say that you'll be explaining these rules and their notation in the rest of this section.

> l 275: Constructor instr-fetch-0-upd is also used to retrieve the head element of a list, however storing its value in an existing variable, represented by the de Bruijn index idx : (x′ , τ′) ∈ Γ.

Why is it necessary to have two versions of the instr-fetch-0-* rules?  I'd have expected instr-fetch-0-new to suffice.

Similarly for the other *-upd variant rules.

> l 290: Block

The block rules in S4 only have a single context, but this data type has two.  Why?

The Γ' in block-jump is unconstrained, which seems odd.

> l 305: We omit the Agda encoding of the subtyping relation for brevity

Brevity is not a major concern for a journal paper.

Put it in a figure?

> l 321 [and elsewhere]: -- some code omitted for brevity

Please include.

Can you say something about how your ⊓ compares with the definition of ⊔ in, e.g., the Coq code of Appel et al.?


# S6

It would make it easier for readers to see how your encoding corresponds to Appel et al. if you would include a figure that summarizes the declarative small-step semantics from Appel et al.

> l 369: Both type environments are used to

What do you mean by "type environments"?  The previous sentence talks about plain environments.  You're using the terminology "typing context" in other places.

> l 372: Env Γ = All (λ(x , τ) → Val τ) Γ

It's still puzzling why identifiers occur in typing contexts.

> Footnote 7

Where is the online repository?

> l 413: instr-branch-nil {l = i} v l s

It looks odd that you have two variables named l in this pattern.  Is this really accepted by Agda?

> l 414: []=⇒lookup l

What does this lemma say, and why is it needed here?

The "rewrite" feature is quite unfamiliar to non-Agda people.  Again, it seems odd that you have an Agda background section (S2) that gives a very basic introduction to Agda but then assume familiarity with sophisticated Agda features in the rest of the paper.  I would propose to add a sentence, or maybe a footnote, whenever you use a feature that would cause non-Agda people to stumble.

> These lemmas and their proofs can be found in our repository online.

It would really help understand what's going on if you would include this in the paper.

Also, you should really include a URL in the paper.

> Since we are using an intrinsically-typed syntax, only valid (well-typed) instructions are accepted in each step of evaluation.

This seems to follow from the type that you gave to run-step, which is making use of intrinsically-typed syntax to encode a preservation property that Agda is helping to enforce in each case of run-step.  (I think that's what you're trying to say, but I found your phrasing somewhat confusing.)


# S7

What is a CheckedInstr?

Is your approach to type checking similar to the approach in the Agda docs?  https://agda.readthedocs.io/en/v2.6.1.3/language/syntactic-sugar.html#example

That approach enforces an additional safety property of type checking: a type checker does not lose any structure that was in the original, untyped, AST.

The one case you show seems to correspond to the approach in the Agda docs.  Cite it, or (better) cite Ulf Norell's Agda tutorial where this approach seems to have first occurred.

There's code in S8 that assumes familiarity with the code that you're not showing or even discussing in this section. :(


# S8

S8.1 is hard to read and full of typos.  Please proof-read.  I would recommend to stick closer to the explanations Appel et al. give for indirect jumps.  I had to read their paper to make sense of what you wrote in S8.1.  I think this section needs rewriting.

Also, it would help readability if S8.1 is only about background, and you have a new subsection about your Agda development.  The beginning and end of S8.1 contains details about your Agda development.  Put that into a section of its own.

S8.1:
- Why are none of the rules in this section named?
- I think you mean ⊂ instead of <: in all the rules of this section.
- Some of the rules in this section use ⊔ and some use ⊓.  Which is it?
- l 536: ommited -> mitted
- l 537: rules -- Some of these rules seem to follow from the commutativity rules you say you omit and the rules you gave earlier in the section?
- p 25 top: The last rule show -> The last rule show_s_
- l 546: This sentence is broken.

S8.2:
- l 588: the "-- same code from before" comment refers to code that you have not shown before.  In general, all of this code is hard/impossible to understand because you do not explain your setup in S7.


# S9

Numbers look great.  You should provide a URL to your repository so readers can validate them.

You should also provide a summary of what the Twelf and Coq developments do and how/why the numbers differ in your approach for each of the 14 bulletpoints that this section discusses.

> 5. Derive an example of type-checking.

You say you use 1 LOC but your explanation in this paragraph suggests you make use of the type checker sketched in S7 and S8.2 which is clearly more than 1 LOC.

> 6. State properties of the least common supertype. This is trivial, since it is just a matter to encode the desired properties as Agda function types

I don't understand what this means?  Show some code?

> 10. Asymptotically efficient algorithm. Our current implementation of the type-checker takes quadratic time.

Your explanation seems to suggest you do not implement a symptotically efficient algorithm, but the number in the table suggests you do?


# S10

Consider also citing Wadler and Kokke's PLFA book which makes a similar observation that intrinsically typed syntax reduces proof effort.

I think you should discuss potential limitations of the intrinsically-typed approach too.  Could you define a dependently-typed object language as a definitional interpreter?

> As future work, we want to reuse the ideas presented in this paper to provide an intrinsically-typed formalization for real-world low-level languages like the eBPF and the LUA VM.

Citations and/or URLs?
