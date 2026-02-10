#!/bin/bash
# Watchdog: restarts tm worker if it dies
cd "$(dirname "$0")"

while true; do
    if tm worker status 2>&1 | grep -q "Running"; then
        sleep 120
    else
        echo "[$(date -u)] Worker dead, restarting..."
        curl -s -H "Title: erdos-728b worker died" -H "Priority: high" -d "Restarting worker at $(date -u)" https://ntfy.sh/gigahector-vps
        tm worker start --background
        sleep 60
    fi
done
