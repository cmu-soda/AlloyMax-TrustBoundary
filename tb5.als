/*************************************
 * Component definitions
 ************************************/
abstract sig Component {
	// The set of services that a component provides (as ports in C&C view)
	services: set Service,

	// Initial architecture of the system, this is used to find the set of
	// compromised components
	initConn: Component -> Service,
	// Helper relation to show the dataflow connections
	initDataflow: set Component,
	// Helper relation to show the data that a component can access
	initCanAccess: set Data,

	newConn: Component -> Service,
	newDataflow: set Component,
	newCanAccess: set Data
}

abstract sig AdminStation extends Component {}
one sig AdminStation1 extends AdminStation {}

abstract sig PaymentManager extends Component {}
one sig PaymentManager1 extends PaymentManager {}

abstract sig PatientMonitor extends Component {}
one sig PatientMonitor1 extends PatientMonitor {}

abstract sig PatientRecord extends Component {}
one sig PatientRecord1 extends PatientRecord {}

abstract sig NursingStation extends Component {}
one sig NursingStation1 extends NursingStation {}

abstract sig PhysicianStation extends Component {}
one sig PhysicianStation1 extends PhysicianStation {}

abstract sig OrderEntry extends Component {}
one sig OrderEntry1 extends OrderEntry {}

// Allow synthesizing new types of components
sig NewComponent extends Component {}

/*************************************
 * Architecture constraints
 ************************************/
fun dataflow[conn: Component -> Component -> Service]: Component -> Component {
	conn.Service + ~(conn.Service)
}

// If A is connected to B, then B is also connected to A
pred biconnected[conn: Component -> Component] {
  all disj c1, c2: Component | c1 -> c2 in conn implies c2 -> c1 in conn
}

// No self-loop in connections
pred noSelfLoop[conn: Component -> Component] {
  all c: Component | c -> c not in conn
}

pred validArch[conn: Component -> Component] {
  noSelfLoop[conn]
  biconnected[conn]
}

// Initial architecture
fact {
	initConn =
		AdminStation1 -> PatientRecord1 -> CreateBill +
		AdminStation1 -> PatientRecord1 -> GetOrderHistory +
		AdminStation1 -> PaymentManager1 -> GetPayment +
		PaymentManager1 -> PatientRecord1 -> GetBill +
		NursingStation1 -> PatientMonitor1 -> GetStatus +
		NursingStation1 -> PatientRecord1 -> GetRecord +
		NursingStation1 -> PatientRecord1 -> AddRecord +
		NursingStation1 -> OrderEntry1 -> GetOrder +
		PhysicianStation1 -> PatientRecord1 -> GetRecord +
		PhysicianStation1 -> PatientRecord1 -> GetOrderHistory +
		PhysicianStation1 -> OrderEntry1 -> CreateOrder +
		OrderEntry1 -> PatientRecord1 -> AddOrderHistory
	
	initDataflow = dataflow[initConn]
	validArch[initDataflow]
}

// New architecture
fact {
	newDataflow = dataflow[newConn]
	validArch[newDataflow]
}

/*************************************
 * Data
 ************************************/
abstract sig Data {}
one sig PatientID, Record, Status, Order, OrderHistory, Bill, Payment extends Data {}

fun canAccess[c: Component, conn: Component -> Component -> Service]: set Data {
	// by being invoked + by invoking other services
	{s: c.services | some p: Component | p -> c -> s in conn}.input +
		Component.(c.conn).output
}

fact {
	all c: Component | c.initCanAccess = canAccess[c, initConn]
	all c: Component | c.newCanAccess = canAccess[c, newConn]
}

/*************************************
 * Services
 ************************************/
abstract sig Service {
	input, output: set Data
}

// AdminStation, has no ports

// PaymentManager
one sig GetPayment extends Service {} {
	input = PatientID
	output = Payment
}

// PatientMonitor
one sig GetStatus extends Service {} {
	input = PatientID
	output = Status
}

// PatientRecord
one sig GetRecord extends Service {} {
	input = PatientID
	output = Record
}
one sig AddRecord extends Service {} {
	input = Record + PatientID
	output = none
}
one sig GetOrderHistory extends Service {} {
	input = PatientID
	output = OrderHistory
}
one sig AddOrderHistory extends Service {} {
	input = PatientID + OrderHistory
	output = none
}
one sig GetBill extends Service {} {
	input = PatientID
	output = Bill
}
one sig CreateBill extends Service {} {
	input = PatientID + Bill
	output = none
}

// NursingStation, has no ports
// PhysicianStation, has no ports

// OrderEntry
one sig GetOrder extends Service {} {
	input = PatientID
	output = Order
}
one sig CreateOrder extends Service {} {
	input = PatientID + Order
	output = none
}

fact {
  AdminStation.services = none
  PaymentManager.services = GetPayment
  PatientMonitor.services = GetStatus
  PatientRecord.services =
    GetRecord + AddRecord +
    GetOrderHistory + AddOrderHistory +
    GetBill + CreateBill
  NursingStation.services = none
  PhysicianStation.services = none
  OrderEntry.services = GetOrder + CreateOrder
}

fun serviceProviders[s: Service]: set Component {
  services.s
}

/*************************************
 * Functional requirements
 ************************************/
pred safelyInvoke[initiator: Component, service: Service,
				  conn: Component -> Component -> Service,
				  compromised: set Component] {
	some provider: serviceProviders[service] |
		safelyInvoke[initiator, provider, service, conn, compromised]
}

pred safelyInvoke[initiator, provider: Component, service: Service,
				  conn: Component -> Component -> Service,
				  compromised: set Component] {
	provider -> service in initiator.conn
	initiator !in compromised
	provider !in compromised
}

pred monitorPatient[conn: Component -> Component -> Service, compromised: set Component] {
	some nursingStation: NursingStation {
		safelyInvoke[nursingStation, GetStatus, conn, compromised]
		safelyInvoke[nursingStation, AddRecord, conn, compromised]
	}
}

pred billManagement[conn: Component -> Component -> Service, compromised: set Component] {
	some db: Component {
		some orderEntry: OrderEntry {
			safelyInvoke[orderEntry, db, AddOrderHistory, conn, compromised]
		}
		some adminStation: AdminStation {
			safelyInvoke[adminStation, db, GetOrderHistory, conn, compromised]
			safelyInvoke[adminStation, CreateBill, conn, compromised]
			safelyInvoke[adminStation, GetPayment, conn, compromised]
		}
	}

}

/*************************************
 * Trust boundary computation
 ************************************/
sig MonitorPatientTB in Component {}
sig BillManagementTB in Component {}

// All compromised components should be connected
//pred attackModel[conn: Component -> Component] {
//	some attack: Component -> Component | all disj c1, c2: Compromised {
//		c1 -> c2 in ^attack
//		attack in conn
//		(attack.Component + Component.attack) in Compromised
//	}
//}

run TB1 {
	monitorPatient[initConn, Component - MonitorPatientTB]
	maxsome Component - MonitorPatientTB
}

run TB2 {
	billManagement[initConn, Component - BillManagementTB]
	maxsome Component - BillManagementTB
}

/*************************************
 * Adaptation under attack
 ************************************/
sig Compromised in Component {}

run Adaptation {
	Compromised = PatientRecord

	monitorPatient[newConn, Compromised]
	billManagement[newConn, Compromised]
	
//	softno NewComponent // softno is better, but SAT4JMax does not support it
	minsome NewComponent
	maxsome newConn & initConn
//	softno newConn - initConn
	minsome newConn - initConn
//	all c: NewComponent | minsome c.services
} for 3 NewComponent

/*************************************
 * Redesign for no overlapping trustboundaries
 ************************************/
run NoOverlap {
	monitorPatient[newConn, Component - MonitorPatientTB]
	billManagement[newConn, Component - BillManagementTB]
	no MonitorPatientTB & BillManagementTB

	maxsome Component - MonitorPatientTB
	maxsome Component - BillManagementTB

//	softno[1] NewComponent // softno is better, but SAT4JMax does not support it
	minsome[1] NewComponent
	maxsome[1] newConn & initConn
	minsome[1] newConn - initConn
//	softno[1] newConn - initConn
//	all c: NewComponent | minsome[1] c.services
} for 3 NewComponent
