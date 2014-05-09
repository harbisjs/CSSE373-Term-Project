sig Data{}

sig Packet{
	insideData: one Data
}

sig Sender{
//	sendData: one Data
	buffer: some Data
}

sig Reciever{
//	receivingData: one Data
	buffer: some Data
}

sig SystemState{
	currentSender: one Sender,
	currentReciever: one Reciever,
	inFlight: lone Packet
}

pred sendPacket{
	some disj s1, s2: SystemState |
		
		s1.currentSender in Sender - s2.currentSender
		and
		s1.currentReciever not in Reciever - s2.currentReciever

		and
		(no p:Packet | p in s1.inFlight)
		and
		(one p:Packet | p in s2.inFlight)


		and
		(
		one d: Data |
			d in s2.inFlight.insideData and d in s1.currentSender.buffer

			and d not in s2.currentSender.buffer and d not in s1.inFlight.insideData

			and d not in s1.currentReciever.buffer and d not in s2.currentReciever.buffer
			
			and 
			// all data initially in the buffer other than the data sent is still in the buffer
			(all senderData : s1.currentSender.buffer - d | senderData in s2.currentSender.buffer)
			and
			// no new data entered the buffer
			(all senderData : Data - (s1.currentSender.buffer - d) | senderData not in s2.currentSender.buffer)
			and
			(all recieverData : s1.currentReciever.buffer | recieverData in s2.currentReciever.buffer)
			and
			(all recieverData : Data - s1.currentReciever.buffer | recieverData not in s2.currentReciever.buffer)
		)
}

pred recievePacket{
	some disj s1, s2: SystemState |
		
		// the senders are the same
		s1.currentSender not in Sender - s2.currentSender
		and
		// the recievers are different
		s1.currentReciever in Reciever - s2.currentReciever

		and
		(one p:Packet | p in s1.inFlight)
		and
		(no p:Packet | p in s2.inFlight)

		and
		(
		one d: Data |
			// the data was in flight and is now in the buffer			
			d in s1.inFlight.insideData and d in s2.currentReciever.buffer
			// the data was not initially in the reciever buffer and is no longer in flight
			and d not in s1.currentReciever.buffer and d not in s2.inFlight.insideData
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
			(all recieverData : s1.currentReciever.buffer + d | recieverData in s2.currentReciever.buffer)
			and
			// no data other than what was originally in the buffer or has now arrived is in the new buffer
			(all recieverData : Data - (s1.currentReciever.buffer + d) | recieverData not in s2.currentReciever.buffer)
		)
}

// final state leads to no state
// all states have something leading to them unless they are the init state


run sendPacket for 2

run recievePacket for 2










