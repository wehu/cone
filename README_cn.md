# Cone-lang

这是一个概念证明项目，目的是试图开发一个语言以适用AI深度学习。
Cone是一门函数式编程语言，基于algebraic effect handlers来隔离副作用，支持可微编程，同时和python生态无缝融合。

## 特点

Cone的主要特点如下：

* 函数式编程
* 支持张量操作
* 支持可微分编程
* 支持algebraic effect handlers
* 支持和python无缝交互
* 使用python package作为包管理

### 函数式

Cone的一个主要目标是作为AI编程前端语言。在AI深度学习邻域，用户要描述的是数学计算表达式，这个是非常符合函数式编程的范式的。无副作用在这里会让整个设计变得简单，同时可以更好的做自动微分。

### 可微编程

```haskell
fun sin(x: f32) : f32
fun cos(x: f32) : f32

diff sin wrt(x) = cos
diff sin(x, dx) -- will call sin's diff function
```

### Algebraic effect handlers

为了能隔离副作用，可以使用algebraic effect把副作用标记出来，然后以绑定的方式来处理，同时简化自动微分和优化。

这里借鉴koka的设计，每个函数的类型标记如下：

```haskell
fun foo(x: i32)   :       e        i32
            |             |         |
         arg-type   effect-type  result-type
```

### 内联底层代码

builtin的函数本身就是内联的底层代码。支持python或者其他语言。同时任何函数也可以用高性能的底层代码来实现。

```haskell
fun sin(x: a) : a {
  inline_python<a>("____result = sin(x)")
}   
```

### 与python的无缝交互

支持import python包，实现方式是最简单的方式是直接生成python代码已经对应动态链接库，并把需要暴露的函数在生成的python包里面绑定成python函数。

张量类型和numpy可以直接互换，其他基本类型也尽量一一对应。

### 使用python的包管理器

直接生成python包。

## Install

安装stack

```bash
curl https://get-ghcup.haskell.org -sSf | sh
```

编译运行例子

```bash
stack run -- run examples/mnist
```




