# Curly
Curly (this variant) is a purely functional, OOP language implemented in Plait--a dialect of Racket. Majorly WIP!

Curly is composed of modular layers as follows:

+ `utils.rkt` holds various helper functions that don't require knowledge of any other modules.
+ `class.rkt` is a bare bones, untyped class system, no inheritance. This level is where all of the interpreting happens.
+ `inherit.rkt` adds (single) inheritance to the class system.
+ `types.rkt` defines Curly types, adds a typed variant of the class system, and adds bare-bones Java-like interfaces, but with no fields, and no default implementations available.
+ `typecheck.rkt` does what you think it would. Static type checking, that is.
+ `parse-ext.rkt` adds an extensible s-expression parser supporting simple `defmacro` style macros.
+ `typed-parse.rkt` this is, conceptually, the public API, and the default parser implementation.

### Some Features:
Single inheritance, Interfaces with multiple inheritance, Built in number primitive types, class types, and interface types, extensible parser.

### TODO:
- [ ] Add a pre-processing layer to flatten out the class hierarchy at parse time in order to facilitate constant time least-upper-bound calculations for intersection types and arms of conditional expressions.
