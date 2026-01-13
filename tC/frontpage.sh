#!/bin/bash
# DashNews Front Page - Decaying Hotness Algorithm
# Usage: ./frontpage.sh [count]

REPO="dropbox/dashnews"
LIMIT=${1:-10}
GRAVITY=1.8

gh issue list -R "$REPO" --state open --limit 100 \
  --json number,title,reactionGroups,createdAt,labels \
  --jq "
    def upvotes: ([.reactionGroups[]? | select(.content == \"THUMBS_UP\") | .users | length] | add) // 0;
    def downvotes: ([.reactionGroups[]? | select(.content == \"THUMBS_DOWN\") | .users | length] | add) // 0;
    def age_hours: (now - (.createdAt | fromdateiso8601)) / 3600;
    def label_names: [.labels[]?.name];
    def is_disputed: (label_names | any(. == \"disputed\"));
    def penalty: if is_disputed then 0.5 else 1 end;
    def hotness: ((upvotes - downvotes + 1) / pow(age_hours + 2; $GRAVITY)) * penalty;
    def status: if (label_names | any(. == \"verified\")) then \" [verified]\"
                elif (label_names | any(. == \"disputed\")) then \" [disputed]\"
                else \"\" end;
    def clean_title: .title | sub(\"^\\\\[(Show DN|Ask DN|Bug Found|RFC|Progress|Lesson Learned|Announcement|Help Wanted)\\\\] \"; \"\");
    [.[] | {
      number,
      title: clean_title,
      score: hotness,
      up: upvotes,
      down: downvotes,
      age_h: (age_hours | floor),
      status: status
    }]
    | sort_by(.score) | reverse | .[:$LIMIT]
    | .[] | \"#\\(.number) [+\\(.up)/-\\(.down) \\(.age_h)h] \\(.title)\\(.status)\"
  "
