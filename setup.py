from __future__ import annotations

from setuptools import find_packages, setup


src_packages = find_packages("src")
agent_packages = find_packages(".", include=["agent*"])

setup(
    packages=src_packages + agent_packages,
    package_dir={
        "": "src",
        "agent": "agent",
        "agent.examples": "agent/examples",
        "agent.integrations": "agent/integrations",
    },
)
