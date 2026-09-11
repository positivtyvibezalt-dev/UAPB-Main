local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "PlasmaLine", function(data)
		if not data.Target or not DungeonsTiming.number(data.Start) or not DungeonsTiming.count(data.Hits, 1) then
			return
		end
		if not DungeonsTiming.number(data.DelayBeforeHit) or not DungeonsTiming.number(data.Tick) or typeof(data.CFs) ~= "table" or #data.CFs ~= data.Hits then
			return
		end
		local events = {}
		for index, origin in ipairs(data.CFs) do
			events[index] = { when = data.DelayBeforeHit + (index - 1) * data.Tick, origin = origin }
		end
		return events, data.Start
	end)
end
