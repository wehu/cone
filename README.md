# Cone-lang

Cone是一门函数式编程语言，基于algebraic effect handlers来隔离副作用，支持可微编程，同时和python生态无缝融合。

## 特点

Cone的主要特点如下：

* 函数式编程
* 支持张量操作
* 支持可微分编程
* 支持algebraic effect handlers
* 支持内联底层高性能代码
* 支持并行编程
* 支持和python无缝交互
* 使用python package作为包管理

## 设计考量

### 函数式

Cone的一个主要目标是作为AI编程前端语言。在AI深度学习邻域，用户要描述的是数学计算表达式，这个是非常符合函数式编程的范式的。无副作用在这里会让整个设计变得简单，同时可以更好的做自动微分。

### 张量计算

为了更好的支持AI或者高性能计算，在语言层面上支持张量计算原语会给编译器带来优化便利。我们支持张量类型，以及一些特殊的张量计算表达。张量计算表达会参考tensor comprehension，例如：

```haskell
[a[i, j] += b[i, k] * c[k, j]] : tensor<i32, [2, 6]>
```

### 可微编程

AI深度学习的本质是可微编程。为了能达到自动微分，需要一种机制来翻译成微分表示。一种方式是定义macro把函数做基于symbol的自动微分变换。

```haskell
fun sin(x: f32) : f32
fun cos(x: f32) : f32

diff-rule sin -> cos
grad(sin) -- will generate fun d-sin/d-x(x: f32) : f32 = cos x
```

### Algebraic effect handlers

为了能隔离副作用，可以使用algebraic effect把副作用标记出来，然后以绑定的方式来处理，同时简化自动微分和优化。

这里借鉴koka的设计，每个函数的类型标记如下：

```haskell
fun foo(x: i32)   :       e        i32
            |             |         |
         arg-type   effect-type  result-type
```

对于effect需要在后面使用的时候被处理。

### 内联底层代码

builtin的函数本身就是内联的底层代码。支持c或者其他语言。同时任何函数也可以用高性能的底层代码来实现。

```haskell
fun sin(x: a) : a {
  inline_python<a>("(sin(x))")
}   
```

### 支持并行编程

需要支持并行语义。

### 与python的无缝交互

AI的python生态是无法回避的。所以我们不回避，我们变成python生态的一部分。

支持import python包，实现方式是最简单的方式是直接生成python代码已经对应动态链接库，并把需要暴露的函数在生成的python包里面绑定成python函数。

张量类型和numpy可以直接互换，其他基本类型也尽量一一对应。

因为python的函数无法确定是否有副作用，我们假定所有import的python的函数都有特别的effect python。

```haskell
import python as p

fun foo() : python () {
  p.print("python print");
}
```

### 使用python的包管理器

直接生成python包，然后发布。

## Install

安装stack

```bash
curl https://get-ghcup.haskell.org -sSf | sh
```

编译运行例子

```bash
stack run examples/basic.cone
```




