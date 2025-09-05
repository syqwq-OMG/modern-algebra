#let span = math.op("span")
#let Var = math.op("Var")
#let Cov = math.op("Cov")
#let Pr = math.op("Pr")
#let ind = math.op("ind")
#let rank = math.op("rank")
#let trace = math.op("trace")
#let svd = math.op("svd")
#let eye = math.op("eye")
#let ones = math.op("ones")
#let orth = math.op("orth")
#let rows = math.op("rows")
#let cols = math.op("cols")
#let zeros = math.op("zeros")
#let diag = math.op("diag")
#let rref = math.op("rref")
#let hstack = math.op("hstack")
#let vstack = math.op("vstack")
#let null = math.op("null")
#let eigen = math.op("eigen")
#let dim = math.op("dim")
#let atan2 = math.op("atan2")
#let softmax = math.op("softmax")
#let eig = math.op("eig")
#let sign = math.op("sign")
#let const = math.op("const")
#let char = math.op("char")


#let oint = math.integral.cont
#let oiint = math.integral.surf
#let oiiint = math.integral.vol
#let iint = math.integral.double
#let iiint = math.integral.triple
#let argmin = math.op("argmin", limits: true)
#let argmax = math.op("argmax", limits: true)


#set math.mat(delim: "[")
#let pmat = math.mat.with(delim: "(")
#let bmat = math.mat.with(delim: "[")
#let detm = math.mat.with(delim: "|")

// 加法表、乘法表
#let symbol-table(r: 2, c: 2) = table.with(
  rows: r,
  columns: c,
  align: (right+bottom,)+(center+bottom,)*(c - 1),
  stroke: (x, y) => {
    if x == 0 and y == 0 { (right: black + 0.7pt, bottom: black + 0.7pt) } else if x == 0 {
      (right: black + 0.7pt)
    } else if y == 0 { (bottom: black + 0.7pt) }
  },
)
