

// Firmware load protocol using Alloy FIFO modules for message channels
// Implements F_alu protocol (originally written in Murphi) and recovers
// deep security flaw (Figure 7) from
// S. Krstić, J. Yang, D. W. Palmer, R. B. Osborne and E. Talmor, 
// "Security of SoC firmware load protocols,"
// 2014 IEEE International Symposium on Hardware-Oriented Security and Trust (HOST), 
// Arlington, VA, USA, 2014, pp. 70-75, doi: 10.1109/HST.2014.6855571.


open Fifo[Message_type]


one sig Live {
	var foo : set bar
}

one sig bar {}

// Message type declarations

abstract sig Message_type {}

one sig ack, auth_req, auth_rsp, load_fw extends Message_type {}

// Signal type declarations

abstract sig Signal_type {}

one sig active, fw_running, lock_IM, seq_sts_PASS, sts extends Signal_type {}

// Firmware declarations

abstract sig Firmware {}

one sig bad_fw, good_fw extends Firmware {}

// Fifo initialization

one sig drv_to_dev, dev_to_ce, ce_to_dev extends Fifo {
	target : set Agent
}

// Agent declarations

abstract sig Agent {
	var agent_signals : set Signal_type,
	source : set Fifo
}	

one sig drv extends Agent {}

one sig dev extends Agent {
	var SM : lone Firmware,
	var IM : lone Firmware
}

one sig ce extends Agent {}

fact {
	source = drv->drv_to_dev + dev->dev_to_ce + ce->ce_to_dev
	drv_to_dev.target = dev
	dev_to_ce.target = ce
	ce_to_dev.target = dev
	all n : dev_to_ce.nodes | n != n.succ
}

// Tracker declaration

one sig Tracker extends Agent {
	var last_transition : set Transition
}

abstract sig Transition {}

one sig t1, t2_0, t2_good, t2_bad, t3, t4, t5, t6, t8 extends Transition {}


// initial state

fact init {
	no SM
	no IM
	no agent_signals
	no last_transition
	some foo
	no content
}

pred T1 {
	// guard
	some foo

	// action
	// following lines added from f3.m	
	agent_signals' = agent_signals - dev->active - dev->fw_running - dev->seq_sts_PASS
	// agent_messages' = agent_messages - drv_to_dev->load_fw - ce_to_dev->auth_rsp
	Tracker.last_transition' = t1
	no SM'
	some foo'	

	// frame conditions
	IM' = IM 
	stutter
}

pred T2_good {
	// guard
	some foo

	// action
	SM' = dev->good_fw
	send[drv_to_dev, load_fw]
	Tracker.last_transition' = t2_good
	some foo'

	// frame conditions
	agent_signals' = agent_signals
	IM' = IM
}

pred T2_bad {
	// guard
	some foo
	
	// action
	SM' = dev->bad_fw
	send[drv_to_dev, load_fw]
	Tracker.last_transition' = t2_bad
	some foo'

	// frame conditions
	agent_signals' = agent_signals	
	IM' = IM
}

pred T3 {
	// guard
 	ce->lock_IM not in agent_signals
	dev->fw_running not in agent_signals
	dev->active not in agent_signals

	receive_and_send[drv_to_dev, load_fw, dev_to_ce, auth_req]

	// action
	IM' = SM
	agent_signals' = agent_signals + dev->active
	Tracker.last_transition' = t3
	some foo'

	// frame conditions
	SM' = SM
}

pred T4 {
	// guard

	receive_and_send[dev_to_ce, auth_req, ce_to_dev, auth_rsp]

	// action
	IM = dev->good_fw implies 
			agent_signals' = agent_signals + ce->sts + ce->lock_IM
		else 
			agent_signals' = agent_signals - ce->sts + ce->lock_IM

//	agent_messages' = agent_messages - dev_to_ce->auth_req + ce_to_dev->auth_rsp
	Tracker.last_transition' = t4
	some foo'

	// frame conditions
	SM' = SM
	IM' = IM
}

pred T5 {
	// guard
	dev->active in agent_signals

	// action
	receive_and_send[ce_to_dev, auth_rsp, dev_to_ce, ack]
	
	ce->sts in agent_signals implies 
			agent_signals' = agent_signals + dev->seq_sts_PASS
		else agent_signals' = agent_signals
	Tracker.last_transition' = t5
	some foo'

	// frame conditions
	IM' = IM
	SM' = SM
}

pred T6 {
	// guard
	receive[dev_to_ce, ack]
	
	// action
	agent_signals' = agent_signals - ce->lock_IM
	Tracker.last_transition' = t6
	some foo'

	// frame conditions
	IM' = IM	
	SM' = SM
}


pred T8 {
	// guard
	dev->seq_sts_PASS in agent_signals

	// action
	agent_signals' = agent_signals - dev->seq_sts_PASS + dev->fw_running	
	Tracker.last_transition' = t8
	some foo'	

	// frame conditions
	IM' = IM
	SM' = SM
	stutter
}


fact trans {
	always (
		T1 or
		T2_good or
		T2_bad or
		T3 or
		T4 or
 		T5 or
		T6 or
		T8
)
}


// examples, etc

run paper_example {
	T1; T2_good; T3; T1; T2_good; T3; T4; T5; T1; T4; T6; T2_bad; T3; T5; T8
} for 4 but 20 steps 

assert safe {always ((dev->fw_running in agent_signals) implies dev->good_fw in IM)} 

check safe for 4 but 20 steps


