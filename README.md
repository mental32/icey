# icey

## ICE-cold const inline DSTs!

> WARNING: THIS IS SO UB ITS NOT EVEN A JOKE, DO **NOT** USE IT ANYWHERE NEAR PRODUCTION!

Dynamically (at const time) sized, stack allocated, DSTs.

It's called `icey` because I discovered 7 different ICEs related to `const_generics`, `const_evaluatable_checked`, and `const_fn`.

Why did I do this? fun mostly and inspiration from here:

* https://crates.io/crates/stack_dst
