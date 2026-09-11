local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "SassShardResonance", function(data)
		if not data.Target or data.Variant == true or not DungeonsTiming.number(data.Start) or typeof(data.Positions) ~= "table" then
			return
		end
		if not DungeonsTiming.number(data.RingDelay) or not DungeonsTiming.number(data.ShardDelay) or not DungeonsTiming.count(#data.Positions, 1) then
			return
		end
		local events = {}
		for ring, positions in ipairs(data.Positions) do
			if typeof(positions) ~= "table" or not DungeonsTiming.count(#positions, 1) or #events + #positions > 256 then
				return
			end
			for index, origin in ipairs(positions) do
				events[#events + 1] = {
					when = (ring - 1) * data.RingDelay + (index - 1) * data.ShardDelay + 0.8,
					origin = origin,
				}
			end
		end
		return events, data.Start
	end)
end
