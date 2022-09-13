# monkey-rs
This repository is an interpreter of the [monkey](https://monkeylang.org/) language that is implemented by Rust.

## How to use
```
$ git clone git@github.com:kadu-v/monkey-rs.git
$ cd monkey-rs
$ cargo r
```

Then, starting the following prompt.
```
$ monkey> 
```

Let's enjoy!!

## User friendly error message
This interprete report a user friendly error message.  
For example,
```
$ monkey> let x = 1
Parse Error: got token: EOF, expected token: SEMICOLON
let x = 1
          ^
```

```
$ monkey> x + false;
Eval Error: expected a integer type
x + false;
  ^^^^^^^^
```





## Examples
```
$monkey> let x = 1;
()
$ monkey> x + x;
2
$monkey> let fib = fn(x) { if (x == 0) { 0 } else { if (x == 1) { return 1; } else { fib(x - 1) + fib(x - 2) }}}; 
()
$monkey> fib(10)
55
$monkey> let newAdder = fn(a, b) { fn(c) { a + b + c };};
()
$monkey> let adder = newAdder(1, 2);
()
$monkey> adder(8);
11
$ monkey> :q
```