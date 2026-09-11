local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "ShadowflameEruption", function(data)
		if not DungeonsTiming.number(data.Delay) or not DungeonsTiming.alive(data.Enemy) then
			return
		end
		return { { when = data.Delay, origin = data.Target } }
	end)
end
