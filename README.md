categorical-unification
==

An exploration of unification implemented on the categorical representation of terms.

This repository is comparing how term unification behaves on different term representations.
The approach is broken down into four steps.

1) Formalize Cartesian-Closed Categories (see theories/Cat.v)
   Formalize the Simply-typed Lambda Calculus (see theories/Cat.v)

2) Prove that CCCs and the STLC are isomorphic (in progress)

3) Implement term unification for both languages.

4) Prove? that STLC terms that are unifiable are also unifiable in CCC.
   In general, this must be true because we can translate, run the unification
   algorithm, and translate back. However, the question is about the direct
   implementation. How difficult is it to write?

   In order for this to hold, I must implement unification modulo equational
   theories, which will likely be very interesting.

Notes
--
- Unification modulo theories is going to be interesting. Maybe be helpful for
  understanding higher-order unification in MirrorCore.
  - This is likely closely related to higher-order unification which is undecidable
    in general.
  - How does this arise in the categorical understanding?
- This might also be a good place to play around with rewriting (e.g.
  Knuth-Bendix completion) because I will already have syntactic
  languages that should be easy to work with.