local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "FrostGolemSwingSlam", function(data)
		if not data.Target or not DungeonsTiming.number(data.Start) or not DungeonsTiming.count(data.Rounds, 0, 255) then
			return
		end
		if not DungeonsTiming.number(data.RoundDelay) or not DungeonsTiming.number(data.StartDist) or not DungeonsTiming.number(data.RoundMult, 0.001) then
			return
		end
		local center = DungeonsTiming.frame(data.CF)
		if not center then
			return
		end
		local events = {}
		for index = 0, data.Rounds do
			events[index + 1] = {
				when = index * data.RoundDelay,
				origin = center * CFrame.new(0, 0, -data.StartDist * (index * 0.9 + 1) / 2),
				scale = data.RoundMult ^ index,
			}
		end
		return events, data.Start
	end)
end
