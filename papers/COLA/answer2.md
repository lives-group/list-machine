# Reviewer's answers

Reviewer 2
-----------


> Reviewer 2: Thanks for improving your paper. There are still some typos, v.g.: stabilishes, estabishes. 
> I recommend you to use a spell-checker.

Answer: We used a spell-checker to correct these typos. Thanks for your review.


Reviewer 3
----------

> Reviewer 3: The manuscript has been refined to address both major and minor concerns from previous reviews.

Answer: We did our best to fix and clarify all the issues pointed in the previous review round. Thank you!

> My main problem with the refined manuscript is the remaining postulate (end of S9).
> The authors should clarify the extent to which this postulate is inherent to the use of intrinsically-typed syntax or not.
> Concretely: Would it be possible to port the "very modal model" to complete the formalization?  Or would substantial revision of the 
> presented framework be necessary?
> It would be great if you could prove the postulate.

Answer: We provide more details on why we choose to postulate such property: 

"Using a semantics-based characterization of typing, like Appel's solution to the list machine benchmark, has the 
benefit of allowing a direct proof of the coercion property for continuation types. While is certainly possible to 
construct a modal logicinspired model and from it proving this type coercion result, such approach deviates from 
our main objective: construct a solution to the list machine benchmark using intrinsically-typed syntax and 
definitional interpreters. For this reason, we decided to postulate this coercion property and stick with 
our original proposal."


#### Detailed Comments

From the author response:

> d. "The duplication of some rules seems unnecessary and, I think, reveals
> a more important issue: you don't discuss your implementation of
> Γ[v:=τ]. It seems that you can define such an operator and let it
> handle wheter v∈dom(Γ) or not."
>
> Answer:
> I would be curious to hear your answer to this.

Answer: Notation Γ[v:=τ] denotes a context update operation: it associates 
the type τ to variable v in context Γ, replacing older values associated 
with v. We do not mention its Agda implementation because it is straightforward
and already available at the Agda standard library.

The duplication of rules just follows the original presentation of the list machine 
benchmark by Appel et. al.

> l175: host's language type-checker
> host language type checker

Answer: Fixed. Thanks!


> l219 least common supertype τ = τ₁ ⊓ τ₂
> Your Agda formalization in S5 uses ⊔ for the least common supertype.  I think this is a typo.

Answer: Fixed. Thanks!


> 5. Intrinsically-typed syntax
> Be consistent in your title capitalization

Answer: Fixed. Thanks!


> rules on p.29
> The syntax in these rules doesn't match the syntax in S3, nor the syntax in your Agda formalization in S5.

Answer: We changed the paper and the Agda formalization to use a consistent notation. Thanks!

> l849: postulate sub-env
> Typesetting of hyphen is off.

Answer: Fixed. Thanks!


> l853: auxiliar
> auxiliary.  Please run a spell checker.

Answer: Fixed. Thanks!

> l834:
> \textbf{Generate~\LaTeX.} Agda's compiler does have a limited support for typesetting~\LaTeX code.
> However, we find it lacking some important features like omitting code from typesetted output
> and use~\LaTeX math-commands instead of unicode characters for mathematical symbols.

> the past tense of typeset is "typeset", not "typesetted".

Answer: Fixed. Thanks!

> Literate Agda does support omitting code:
> https://agda.readthedocs.io/en/v2.6.1.2/tools/generating-latex.html#breaking-up-code-blocks
> If you mean something else, please clarify.

Answer: We removed the sentence about omitting source code from the typeset output. Thanks!


> l894: by [24]
> Looks like this should have been a \citet or \citeauthor

Answer: Fixed. Thanks!

> l916: metodology
> methodology

Answer: Fixed. Thanks!
