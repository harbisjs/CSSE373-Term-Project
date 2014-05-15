open util/ordering[SystemState]

sig Data {}

sig Packet{
	insideData: one Data
}

one sig AckPacket, NakPacket extends Packet{}

sig Sender{
	buffer: set Data,
	mostRecentlySentData: lone Data
}

sig Receiver{
	buffer: set Data
}

abstract sig PacketStatus { }
one sig Corrupted, NotCorrupted extends PacketStatus { }

sig SystemState{
	currentSender: one Sender,
	currentReceiver: one Receiver,
	inFlight: lone Packet,
	inFlightStatus: lone PacketStatus 
}

fact alwaysPacketStatus{
	all s:SystemState | (one s.inFlight => one s.inFlightStatus) and (no s.inFlight => no s.inFlightStatus)
}

pred sendAckNakPacket[s1, s2 : SystemState] {
	// Send ack or nak packet
	s1.inFlightStatus in Corrupted <=>
	(
		s1.inFlight.insideData in Data
		and
		no d:Data | d in (s2.currentSender.buffer - s1.currentSender.buffer)
		and
		no d:Data | d in (s1.currentSender.buffer - s2.currentSender.buffer)
		and

		no d:Data | d in (s2.currentReceiver.buffer - s1.currentReceiver.buffer)
		and
		no d:Data | d in (s1.currentReceiver.buffer - s2.currentReceiver.buffer)
		and
		// sending the nak packet
		s2.inFlight in NakPacket
		and
		s2.inFlightStatus in PacketStatus
	)
}

pred testSendAckNakPacket{
	some disj s1, s2 : SystemState | s1.inFlightStatus in Corrupted and Corrupted in s1.inFlightStatus and sendAckNakPacket[s1, s2]
}

run testSendAckNakPacket for 2

pred receiveAckNakPacket[s1, s2 : SystemState]{
	// Receive ack or nak
}

pred sendPacket[s1, s2 : SystemState]{

		no s1.currentSender.mostRecentlySentData

		and
		//the senders are different
		s1.currentSender in Sender - s2.currentSender
		and
		//the receivers are the same
		s1.currentReceiver not in Receiver - s2.currentReceiver

		and
		//initially nothing in flight
		(no p:Packet | p in s1.inFlight)
		and
		//after only one packet in flight
		(one p:Packet | p in s2.inFlight)


		and
		(
		one d: Data |
			//the data came from the sender buffer and is now in flight
			d in s2.inFlight.insideData and d in s1.currentSender.buffer
			//the data did not start in flight and did not end up in the sender buffer
			and d not in s2.currentSender.buffer and d not in s1.inFlight.insideData
			//the data is not in any receiver buffer
			and d not in s1.currentReceiver.buffer and d not in s2.currentReceiver.buffer
			
			and 
			// all data initially in the buffer other than the data sent is still in the buffer
			(all senderData : s1.currentSender.buffer - d | senderData in s2.currentSender.buffer)
			and
			// no new data entered the buffer
			(all senderData : Data - (s1.currentSender.buffer - d) | senderData not in s2.currentSender.buffer)
			and
			//nothing got lost from the receiver buffer
			(all receiverData : s1.currentReceiver.buffer | receiverData in s2.currentReceiver.buffer)
			and
			//nothing got added in the receiver buffer
			(all receiverData : Data - s1.currentReceiver.buffer | receiverData not in s2.currentReceiver.buffer)
		)
}

pred receivePacket[s1, s2: SystemState]{



		s1.inFlightStatus in NotCorrupted
		and
		// the senders are the same
		s1.currentSender not in Sender - s2.currentSender
		and
		// the receivers are different
		s1.currentReceiver in Receiver - s2.currentReceiver

		and
		//initially one packet in flight
		(one p:Packet | p in s1.inFlight)
		and
		//after nothing in flight
		(no p:Packet | p in s2.inFlight)

		and
		(
		one d: Data |
			// the data was in flight and is now in the buffer			
			d in s1.inFlight.insideData and d in s2.currentReceiver.buffer
			// the data was not initially in the receiver buffer and is no longer in flight
			and d not in s1.currentReceiver.buffer and d not in s2.inFlight.insideData
			// the data was never in the sender buffer before or after
			and d not in s1.currentSender.buffer and d not in s2.currentSender.buffer
			
			and 
			// all data originally in the sender buffer is still in there
			(all senderData : s1.currentSender.buffer | senderData in s2.currentSender.buffer)
			and
			// no new data has entered the sender buffer
			(all senderData : Data - (s1.currentSender.buffer) | senderData not in s2.currentSender.buffer)
			and
			// all data that was either originally in the buffer or that has arrived is in the buffer
			(all receiverData : s1.currentReceiver.buffer + d | receiverData in s2.currentReceiver.buffer)
			and
			// no data other than what was originally in the buffer or has now arrived is in the new buffer
			(all receiverData : Data - (s1.currentReceiver.buffer + d) | receiverData not in s2.currentReceiver.buffer)
		)
}

pred finalState[s: SystemState]{
	s.currentReceiver.buffer = Data 
	no s.currentSender.buffer
	no s.inFlight
}

pred init[s: SystemState]{
	s.currentSender.buffer = Data 
	no s.currentReceiver.buffer
	no s.inFlight	
}

/*
fact traceFullTransition{
	init[first]
	all s:SystemState - last |
		let s' = s.next |
			sendPacket[s, s'] or receivePacket[s, s']
}
*/
fact trimExtraPackets{
	all d:Data| one p:Packet | d in p.insideData
}

fact trimExtraSenders{
	all disj s1, s2: Sender | s1.buffer not = s2.buffer
}

fact trimExtraReceivers{
	all disj s1, s2: Receiver | s1.buffer not = s2.buffer
}

pred allDataGetsThroughPred{
	some s: SystemState |
		finalState[s]
}

assert allDataGetsThrough{
	not( some s: SystemState |
		finalState[s])
}

pred failureState[s:SystemState] {
	no s.inFlight
	no s.currentSender.buffer
	some d:Data| d not in s.currentReceiver.buffer
}

assert allDataDoesNotGetThrough{
	not some s:SystemState |	failureState[s]
}

check allDataGetsThrough for 5 but exactly 2 Data
check allDataDoesNotGetThrough for 5 but exactly 2 Data

run sendPacket for 2

run receivePacket for 2

run finalState for 5 but exactly 2 Data
run init for 3 but exactly 2 Data
