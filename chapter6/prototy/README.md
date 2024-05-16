# Artifact: CP Compiler with References

This artifact includes an implementation of imperative compositional programming, i.e. a compiler for CP with imperative features like references. CP is a *compositional* programming language, founded on a core calculus named *Fim+*. 

## Quick Start

- First of all, you need to install [Node.js](https://nodejs.org).
- Then execute `npm install` to get all of the dev dependencies.
- After installation, execute `npm start` to install PureScript libraries and run a REPL;
- Inside the REPL, use  `:compile` commands to execute CP programs.

## REPL Example

```
$ npm start

> cp-next@0.1.3 start
> spago run

[info] Installing 72 dependencies.
......
[info] Build succeeded.

Next-Gen CP REPL, dev version

> :compile examples/Prog1.cp
true: [ ]
 x = true: [ ]
  false: [ x; ]
   y = false: [ x; ]
    x: [ x; y; ]
     y: [ y; ]
      x = y: [ y; ]
     x: [ x; ]
      z = not x: [ ]
()
> :compile examples/Prog2.cp
10: [ ]
 x = 10: [ ]
  x: [ x; ]
   0: [ x; ]
    x: [ x; ]
     1: [ x; ]
      y = (x + 1): [ x; ]
       <Phi>: [ x; y; ]
        x: [ x; y; ]
         y: [ y; ]
          z = (x + y): [ ]
    x: [ x; ]
     1: [ x; ]
      y = (x - 1): [ x; ]
```
