# Cone-lang

This is a POC project and attempt to develop a language for AI. Cone-lang is a functional language, 
which handles with side-effect by algebraic effect handlers, supports autodiff and integrates with python seamlessly.

## Features

* Functional programming
* Support tensor type and operations
* Support autodiff
* Support algebraic effect handlers
* Seamlessly integrate with python
* Use python package as package management

### Autodiff

```haskell
fun sin(x: f32) : f32
fun cos(x: f32) : f32

diff sin wrt(x) = cos
diff sin(x, dx) -- will call sin's diff function
```

### Algebraic effect handlers

Learning from [Koka-lang](https://koka-lang.github.io/koka/doc/book.html), the type annotation of function as below:

```haskell
fun foo(x: i32)   :       e        i32
            |             |         |
         arg-type   effect-type  result-type
```

### Integration with python

Inline python code and generate the python package for package release

```haskell
fun sin(x: a) : a {
  inline_python<a>("____result = sin(x)")
}   
```

## Install

Install stack

```bash
curl https://get-ghcup.haskell.org -sSf | sh
```

Run mnist example

```bash
stack run -- run examples/mnist
```