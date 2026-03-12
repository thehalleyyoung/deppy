"""TensorGuard-style shape bug adapted from halley-labs/tensorguard/examples.

This remains a useful example of a bug that TensorGuard's tensor semantics can
reason about, even when the current DepPy native-Python static layer does not
fully discharge it yet.
"""
import torch.nn as nn


class BuggyModel(nn.Module):
    def __init__(self):
        super().__init__()
        self.conv = nn.Conv2d(3, 128, 3, padding=1)
        self.pool = nn.AdaptiveAvgPool2d(1)
        self.fc = nn.Linear(256, 10)

    def forward(self, x):
        x = self.conv(x)
        x = self.pool(x)
        x = x.flatten(1)
        x = self.fc(x)
        return x
