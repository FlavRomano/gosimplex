package main

import (
	"fmt"
	"sort"

	"gonum.org/v1/gonum/mat"
)

func index_of(slice []int, k int) int {
	i := 0
	for i < len(slice) {
		if slice[i] == k {
			return i
		}
		i++
	}
	return -1
}


func slice_remove(slice []int, i int) []int {
	return append(slice[:i], slice[i+1:]...)
}


func int_In_Slice(x int, list []int) bool {
    for _, y := range list {
        if y == x {
            return true
        }
    }
    return false
}


func print_mat(m int, n int, data []float64) string {
	a := mat.NewDense(m, n, data)
	fa := mat.Formatted(a, mat.Prefix(""),mat.FormatMATLAB())
	s := fmt.Sprintf("%.1f", fa)
	return s
}


func soluzione_primale_base_amm(A mat.Dense, b mat.Dense) mat.Dense {
	var inv_A mat.Dense
	var x mat.Dense
	inv_A.Inverse(&A)
	x.Mul(&inv_A,&b)

	inv_A_string := print_mat(len(b.RawMatrix().Data),len(b.RawMatrix().Data),inv_A.RawMatrix().Data)
	b_string := print_mat(len(b.RawMatrix().Data),1,b.RawMatrix().Data)
	x_string := print_mat(len(b.RawMatrix().Data),1,x.RawMatrix().Data)
	fmt.Printf("\tx = %v * %v = %v\n", inv_A_string, b_string, x_string)
	return x
}


func soluzione_duale(c mat.Dense, A mat.Dense, b mat.Dense, base []int) ([]float64, bool, int, int) {
	var yB mat.Dense
	var inv_A mat.Dense
	y := []float64{}
	inv_A.Inverse(&A)
	yB.Mul(&c,&inv_A)
	for i := 0; i <= len(A.RawMatrix().Data); i++ {
		y = append(y, 0)
	}
	for i,j := range base {
		y[j-1] = yB.RawMatrix().Data[i]
	}

	inv_A_string := print_mat(len(b.RawMatrix().Data),len(b.RawMatrix().Data),inv_A.RawMatrix().Data)
	c_string := print_mat(len(c.RawMatrix().Data),1,c.RawMatrix().Data)
	y_string := print_mat(1,len(b.RawMatrix().Data),yB.RawMatrix().Data)

	//calcolo indice uscente
	cond := true
	real_h := -1
	for i,j := range y {
		if j < 0 {
			cond = false
			real_h = i
			break
		}
	}

	fmt.Printf("\tyB = %v * %v = %v\n", c_string, inv_A_string, y_string)
	if real_h > 0 {
		fmt.Printf("\ty = %.1f => h = %v\n", y, real_h+1)
	}

	h := -1
	for i,j := range yB.RawMatrix().Data {
		if j < 0 {
			h = i
			break
		}
	}

	return y, cond, h, real_h+1
}


func dir_crescita(A, AB, b, c mat.Dense, base, not_base []int, h int) (mat.Dense, []int, bool) {
	var tmp mat.Dense
	var xi mat.Dense
	var data_inv_AB []float64
	tmp.Inverse(&AB)
	for _,j := range tmp.RawMatrix().Data {
		data_inv_AB = append(data_inv_AB, -1 * j)
	}
	inv_A := mat.NewDense(len(b.RawMatrix().Data), len(b.RawMatrix().Data), data_inv_AB)
	u := mat.NewDense(len(b.RawMatrix().Data), 1, nil)
	u.Set(h, 0, 1)
	xi.Mul(inv_A,u)

	inv_AB_string := print_mat(len(b.RawMatrix().Data),len(b.RawMatrix().Data),inv_A.RawMatrix().Data)
	u_string := print_mat(len(b.RawMatrix().Data), 1, u.RawMatrix().Data)
	xi_string := print_mat(len(b.RawMatrix().Data),1,xi.RawMatrix().Data)
	fmt.Printf("\txi = %v * %v = %v\n", inv_AB_string, u_string, xi_string)

	//Check condizione problema illimitato
	AN := mat.NewDense(len(not_base), len(c.RawMatrix().Data), nil)	
	for i := 0 ; i < len(not_base); i++ {					
		AN.SetRow(i,A.RawRowView(not_base[i]-1))
	}

	var p mat.Dense
	p.Mul(AN, &xi)

	cond := false

	// for _,j := range p.RawMatrix().Data {
	// 	if j < 0 {
	// 		cond = true
	// 	}
	// }

	return xi, not_base, cond
}


func passo_massimo(A, b, c, x, xi mat.Dense, not_base []int) (float64, int) {
	res := []float64{}
	for _,j := range not_base {
		var m mat.VecDense
		v1 := mat.NewVecDense(len(c.RawMatrix().Data),A.RawRowView(j-1)).TVec()
		v2 := mat.NewVecDense(len(c.RawMatrix().Data), xi.RawMatrix().Data)
		m.MulVec(v1,v2)
		if m.At(0,0) > 0 {
			bi := b.At(j-1,0)
			var q mat.Dense
			q.Mul(v1,&x)
			num := bi - q.At(0,0)
			el := num / (m.At(0,0))
			res = append(res, el, float64(j))
		} 
	}

	// minimum of res
	lambda,k := res[0],res[1] // [lambda0, k0, ..., lambdai-1, ki-1] 
	for i := range res {
		if lambda >= res[i] && i % 2 == 0 {
			lambda = res[i]
			k = res[i+1]
		}
	}

	return lambda, int(k)
}


func simplesso_primale(data_A []float64, data_b []float64, data_c []float64, base []int) {
	A := mat.NewDense(len(data_b), len(data_c), data_A)
	b := mat.NewDense(len(data_b),1, data_b)
	c := mat.NewDense(1, len(data_c), data_c)
	iterazioni := 0
	state := ""

	for state == "" {
		iterazioni++
		not_base := []int{}
		//inizializzazione AB
		AB := mat.NewDense(len(base), len(data_c), nil)	
		for i := 0 ; i < len(base); i++ {					
			AB.SetRow(i,A.RawRowView(base[i]-1))
		}
		//inizializzazione bB
		bB := mat.NewDense(len(base),1,nil)				
		for i := 0 ; i < len(base); i++ {					
			bB.SetRow(i,b.RawRowView(base[i]-1))
		}
		for i := 1; i <= len(AB.RawMatrix().Data)+1; i++ {
			if !int_In_Slice(i, base) {
				not_base = append(not_base, i)
			}
		}
		fmt.Printf("%v. iterazione: B = %v, N = %v\n", iterazioni, base, not_base)
		x := soluzione_primale_base_amm(*AB,*bB)
		y, cond1, h, real_h := soluzione_duale(*c,*AB,*bB,base)

		if !cond1 {
			xi, not_base, cond2 := dir_crescita(*A, *AB,*bB, *c, base, not_base, h)
			if cond2 {
				state = "Problema illimitato"
			} else {
				lambda,k := passo_massimo(*A, *b, *c, x, xi, not_base)
				base = append(base, k)
				base = slice_remove(base, index_of(base, real_h))
				sort.Ints(base)
				fmt.Printf("\tLambda: %v, h: %v, k:%v, Base: %v\n", lambda, real_h, k, base)
				fmt.Println("---------------------------------------------------------------")
			}
		} else {
			fmt.Printf("\nSoluzione ottima: \n\t B = %v, N = %v\n\t x = %v \n\t y = %v\n", base, not_base, x.RawMatrix().Data, y)
			state = "Ottimo"
		}
	}
}


func main() {
	A := []float64{1,-1,0,1,1,1,-1,1,-1,0}
	b := []float64{1,2,3,1,0}
	c := []float64{2,1}
	B := []int{4,5}

	simplesso_primale(A,b,c,B)
}