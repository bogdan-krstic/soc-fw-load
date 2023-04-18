

// relations read, write, and nodes all subsets of Fifo x Node

// Modified from Alloy's example/temporal/buffers.als

module fifo[T]

abstract sig Fifo {
	var read : one Node,
	var write : one Node,
	nodes : set Node}

sig Node {
	succ : one Node,
	var content : lone T
}

fact {
	all f : Fifo | f.read in f.nodes
	all f : Fifo | f.write in f.nodes
	all f : Fifo, n : f.nodes | f.nodes in n.^succ // ^ is non-reflexive transitive closure operator
	all f : Fifo, n : f.nodes | n.succ in f.nodes
	all f, g : Fifo | (f != g) implies (no f.nodes & g.nodes)
	all n : Node | some f : Fifo | n in f.nodes 
}

pred send[f : Fifo, x : T]{
	// guard	
	no f.write.content
	
	// action
	content' = content + f.write->x
	write' = write - f->f.write + f->f.write.succ

	// frame conditions
	read' = read
}

pred receive[f : Fifo, x : T]{
	x = f.read.content

	content' = content - f.read->x
	write' = write
	read' = read - f->f.read + f->f.read.succ
}

pred receive_and_send[f : Fifo, x : T, g : Fifo, y : T]{
	x = f.read.content
	no g.write.content

	content' = content - f.read->x + g.write->y
	write' = write - g->g.write + g->g.write.succ
	read' = read - f->f.read + f->f.read.succ
}

pred stutter {
	content' = content
	write' = write
	read' = read
}

//

