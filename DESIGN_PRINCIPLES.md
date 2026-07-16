# Design Principles

## Readability And Concision

We value readability over concision, and we want concision wherever possible.

Code, definitions, theorem statements, and proof structure should be easy to read
first. Concision is valuable when it removes noise without hiding intent.

## Use Existing Libraries First

We will never reinvent the wheel. Before attempting to implement anything, we
must first determine what we can take from mathlib or other available libraries.

New definitions, lemmas, or abstractions should be added only after checking that
the needed concept is not already available in the imported libraries.

