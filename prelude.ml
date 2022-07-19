let (%) f g = fun x -> f (g x)

let idfun = fun x -> x