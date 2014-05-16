open util/ordering[SystemState]

sig Checksum {}

abstract sig Payload{}

sig DataPayload extends Payload{}
sig Ack extends Payload{}
sig Nak extends Payload{}

sig Packet{
	insideData: one Payload,
	checksum: one Checksum
}

one sig Global {
	checksums: Payload one -> one Checksum
}

fun computeChecksum[p:Payload] : Checksum {
	Global.checksums[p]
}

sig SystemState{
	mostRecentlySent: lone DataPayload,
	senderBuffer: set DataPayload,
	receiverBuffer: set DataPayload,
	inFlight: lone Packet
}

pred sendPacket2[s1, s2 : SystemState]{
(s1.inFlight.checksum = computeChecksum[s1.inFlight.insideData]) => (
	
	s1.inFlight.insideData in Payload - DataPayload
	and
	((no s1.mostRecentlySent) or (s1.inFlight.insideData in Ack)) => sendPacket[s1, s2]
	else
	(retransmitPacket[s1, s2])

	)
	else
	(
		skip[s1, s2]
	)
}

run sendPacket2 for 2

fact cannotBeInSenderAndMostRecentlySent{
	all s:SystemState | no d: DataPayload | d in s.senderBuffer and d in s.mostRecentlySent
}

//pred sendPacket2Tester[]{
//	some disj s1, s2 : SystemState | some p:Packet | p in s1.inFlight and p not in ((Payload - DataPayload) - Ack) and sendPacket2[s1, s2]
//}

//run sendPacket2Tester for 2

run retransmitPacket for 2

pred skip[s1, s2 : SystemState]{
	s1 = s2
}

pred retransmitPacket[s1, s2 : SystemState]{
		//after only one packet in flight
		(one p:Packet | p in s2.inFlight)
		and
		(one p:Packet | p in s1.inFlight)
		and
		(s1.inFlight.insideData in Nak)

		and
		(
		one d: s1.mostRecentlySent |
			d in s2.mostRecentlySent
			and

			//the data came from the sender buffer and is now in flight
			d in s2.inFlight.insideData
			//the data did not start in flight and did not end up in the sender buffer
			and d not in s2.senderBuffer and d not in s1.inFlight.insideData
			//the data is not in any receiver buffer
			and d not in s1.receiverBuffer and d not in s2.receiverBuffer
			
			and 
			// all data initially in the buffer other than the data sent is still in the buffer
			(all senderData : s1.senderBuffer | senderData in s2.senderBuffer)
			and
			// no new data entered the buffer
			(all senderData : DataPayload - (s1.senderBuffer) | senderData not in s2.senderBuffer)
			and
			//nothing got lost from the receiver buffer
			(all receiverData : s1.receiverBuffer | receiverData in s2.receiverBuffer)
			and
			//nothing got added in the receiver buffer
			(all receiverData : DataPayload - s1.receiverBuffer | receiverData not in s2.receiverBuffer)
		)
}

pred sendPacket[s1, s2 : SystemState]{
		
		//after only one packet in flight
		(one p:Packet | p in s2.inFlight)
		

		and
		(
		one d: DataPayload |
			d in s2.mostRecentlySent
			and

			//the data came from the sender buffer and is now in flight
			d in s2.inFlight.insideData and d in s1.senderBuffer
			//the data did not start in flight and did not end up in the sender buffer
			and d not in s2.senderBuffer and d not in s1.inFlight.insideData
			//the data is not in any receiver buffer
			and d not in s1.receiverBuffer and d not in s2.receiverBuffer
			
			and 
			// all data initially in the buffer other than the data sent is still in the buffer
			(all senderData : s1.senderBuffer - d | senderData in s2.senderBuffer)
			and
			// no new data entered the buffer
			(all senderData : DataPayload - (s1.senderBuffer- d) | senderData not in s2.senderBuffer)
			and
			//nothing got lost from the receiver buffer
			(all receiverData : s1.receiverBuffer | receiverData in s2.receiverBuffer)
			and
			//nothing got added in the receiver buffer
			(all receiverData : DataPayload - s1.receiverBuffer | receiverData not in s2.receiverBuffer)
		)
}

run sendPacket for 2

pred receivePacket2[s1, s2: SystemState]{
	(s1.inFlight.checksum = computeChecksum[s1.inFlight.insideData]) => (
		one s1.mostRecentlySent
		and
		s1.inFlight.insideData in DataPayload
		and
		receivePacket[s1, s2]
	)
	else
	(
		one s1.mostRecentlySent
		and
		s1.inFlight.insideData in DataPayload
		and
		receiveCorruptedPacket[s1, s2]
	)	
}

pred receiveCorruptedPacket[s1, s2: SystemState]{
		//initially one packet in flight
		(one p:Packet | p in s1.inFlight)
		and
		//after one packet in flight
		(one p:Packet | p in s2.inFlight and p.insideData in Nak)

		and
		(s1.mostRecentlySent = s2.mostRecentlySent) 

		and
		(
		one d: DataPayload |
			// the data was in flight and is now in the buffer			
			d in s1.inFlight.insideData and d not in s2.receiverBuffer
			// the data was not initially in the receiver buffer and is no longer in flight
			and d not in s1.receiverBuffer and d not in s2.inFlight.insideData
			// the data was never in the sender buffer before or after
			and d not in s1.senderBuffer and d not in s2.senderBuffer
			
			and
			// all data originally in the sender buffer is still in there
			(all senderData : s1.senderBuffer | senderData in s2.senderBuffer)
			and
			// no new data has entered the sender buffer
			(all senderData : DataPayload - (s1.senderBuffer) | senderData not in s2.senderBuffer)
			and
			// all data that was either originally in the buffer is in the buffer
			(all receiverData : s1.receiverBuffer | receiverData in s2.receiverBuffer)
			and
			// no data other than what was originally in the buffer is in the new buffer
			(all receiverData : DataPayload - (s1.receiverBuffer) | receiverData not in s2.receiverBuffer)
	)
}

run receivePacket2 for 2

pred receivePacket[s1, s2: SystemState]{

		//initially one packet in flight
		(one p:Packet | p in s1.inFlight)
		and
		//after one packet in flight
		(one p:Packet | p in s2.inFlight and p.insideData in Ack)
		and
		(s1.mostRecentlySent = s2.mostRecentlySent) 

		and
		(
		one d: DataPayload |
			// the data was in flight and is now in the buffer			
			d in s1.inFlight.insideData and d in s2.receiverBuffer
			// the data was not initially in the receiver buffer and is no longer in flight
			and d not in s1.receiverBuffer and d not in s2.inFlight.insideData
			// the data was never in the sender buffer before or after
			and d not in s1.senderBuffer and d not in s2.senderBuffer
			
			and 
			// all data originally in the sender buffer is still in there
			(all senderData : s1.senderBuffer | senderData in s2.senderBuffer)
			and
			// no new data has entered the sender buffer
			(all senderData : DataPayload - (s1.senderBuffer) | senderData not in s2.senderBuffer)
			and
			// all data that was either originally in the buffer or that has arrived is in the buffer
			(all receiverData : s1.receiverBuffer + d | receiverData in s2.receiverBuffer)
			and
			// no data other than what was originally in the buffer or has now arrived is in the new buffer
			(all receiverData : DataPayload - (s1.receiverBuffer + d) | receiverData not in s2.receiverBuffer)
		)
}

pred finalState[s: SystemState]{
	s.receiverBuffer= DataPayload
	no s.senderBuffer
//	no s.inFlight
}

pred init[s: SystemState]{
	s.senderBuffer = DataPayload
	no s.receiverBuffer
//	no s.inFlight	
	no s.mostRecentlySent
}

fact traceFullTransition{
	init[first]
	all s:SystemState - last |
		let s' = s.next |
			sendPacket2[s, s'] or receivePacket2[s, s']
}

fact trimExtraPackets{
	all d:DataPayload| one p:Packet | d in p.insideData
}

fact trimExtraAcks{
	all d:Ack| one p:Packet | d in p.insideData
}

fact trimExtraNaks{
	all d:Nak| one p:Packet | d in p.insideData
}

/*
fact trimUnconnectedPackets{
	all p:Packet | some s:SystemState | (p in s.inFlight)
}
*/

pred forceOneReceiveError{
	some disj s1, s2:SystemState | receiveCorruptedPacket[s1, s2]
	and
	some s:SystemState | finalState[s]
}

run forceOneReceiveError for 9 but exactly 2 DataPayload

pred allDataGetsThroughPred{
	some s: SystemState |
		finalState[s]
}

assert allDataGetsThrough{
	not( some s: SystemState |
		finalState[s])
}

pred failureState[s:SystemState] {
(
	no s.inFlight
and
	no s.senderBuffer
and
	some d:DataPayload| d not in s.receiverBuffer
)
or
(
	 s.inFlight.insideData in Ack + Nak
	and s.inFlight.checksum != s.inFlight.insideData.computeChecksum[]
)
}

assert allDataDoesNotGetThrough{
	not some s:SystemState |	failureState[s]
}

check allDataGetsThrough for 5 but exactly 2 DataPayload
check allDataDoesNotGetThrough for 5 but exactly 2 DataPayload

run sendPacket for 2

run receivePacket for 2

run finalState for 5 but exactly 2 DataPayload
run init for 3 but exactly 2 DataPayload
